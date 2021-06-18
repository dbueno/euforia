// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include <cassert>
#include <chrono>
#include <csignal>
#include <iostream>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/FileSystem.h>
#include <mathsat.h>
#include <regex>
#include <string>
#include <unordered_map>
#ifdef HAVE_BOOST_IOSTREAMS
#  include <boost/iostreams/filter/gzip.hpp>
// #  include <boost/iostreams/filter/zlib.hpp>
#  include <boost/iostreams/filtering_streambuf.hpp>
#  include <boost/iostreams/copy.hpp>
#endif

extern "C" {
#include <sys/stat.h>
#include <getopt.h>
#include <wordexp.h>
//#include <sys/resource.h>
}

#include "abstract_checker.h"
#include "checker_types.h"
#include "counterexample.h"
#include "git_version.h"
#include "supp/euforia_config.h"
#include "supp/mathsat_vmt_parser.h"
#include "supp/statistics.h"
#include "supp/z3_solver.h"
#include "supp/pp/doc.h"
#include "xsys/abstract_vmt_transition_system.h"
#include "xsys/concrete_vmt_transition_system.h"


using namespace euforia;
using namespace std;
using namespace llvm;
namespace fs = llvm::sys::fs;


namespace {

class MathsatEnvDeleter {
 public:
  MathsatEnvDeleter(msat_env env): env_(env) {}
  ~MathsatEnvDeleter()
  {
    if (!MSAT_ERROR_ENV(env_)) {
      msat_destroy_env(env_);
    }
  }

 private:
  msat_env env_;
};

static string ReadFile(const string& filename) {
#ifdef HAVE_BOOST_IOSTREAMS
  if (ends_with(filename, "gz")) {
    ifstream infile(filename.c_str(), ios::in | ios::binary);
    if (!infile) {
      fmt::print(cerr, "Error reading filename: {}\n", filename);
      exit(1);
    }
    namespace bio = boost::iostreams;
    stringstream decompressed;
    bio::filtering_streambuf<bio::input> out;
    out.push(bio::gzip_decompressor());
    out.push(infile);
    bio::copy(out, decompressed);
    return decompressed.str();
  } else
#endif
  {
    ifstream infile(filename.c_str(), std::ios::in);
    if (!infile) {
      fmt::print(cerr, "Error reading filename: {}\n", filename);
      exit(1);
    }
    ostringstream ss;
    ss << infile.rdbuf();
    return ss.str();
  }
}

} // end namespace

//^----------------------------------------------------------------------------^

// This is a global so that everything in this file can refer to it
static z3::context ctx;
static TimerClock clk;
static TimerClock::time_point start_time;
static bool SVcompOutput = true;
unique_ptr<AbstractChecker> chk;

namespace euforia {

// Storage for configuration
config::Config euforia_config;
extern unsigned euforia_major_version;
extern unsigned euforia_minor_version;

static void PrintFeatures() {
  unsigned z3_major, z3_minor, z3_build_num, z3_rev_num;
  Z3_get_version (&z3_major, &z3_minor, &z3_build_num, &z3_rev_num);

  logger.Log(1, "EUForia version {}.{}", euforia_major_version,
             euforia_minor_version);
  logger.Log(1, "commit {}, branch {}, tag {}",
             git_version, git_branch, git_tag);
  logger.Log(1, "c++ {}", __cplusplus);
  logger.Log(1, "compiled with Z3 version {}.{} [build {}, revision {}]",
             z3_major, z3_minor, z3_build_num, z3_rev_num);
#ifdef GENDATA_FIRST
  logger.Log(1, "GENDATA_FIRST: true");
#else
  logger.Log(1, "GENDATA_FIRST: false");
#endif
#ifdef DIRTYBIT
  logger.Log(1, "DIRTYBIT: true");
#else
  logger.Log(1, "DIRTYBIT: false");
#endif
#ifdef NO_GEN_WITH_UNSAT_CORE
  logger.Log(1, "NO_GEN_WITH_UNSAT_CORE: true");
#else
  logger.Log(1, "NO_GEN_WITH_UNSAT_CORE: false");
#endif
#ifdef CUBE_HISTORY
  logger.Log(1, "CUBE_HISTORY: true");
#else
  logger.Log(1, "CUBE_HISTORY: false");
#endif
#ifdef EXPENSIVECHECKS
  logger.Log(1, "EXPENSIVECHECKS: true");
#else
  logger.Log(1, "EXPENSIVECHECKS: false");
#endif
#ifdef PROPLOC
  logger.Log(1, "PROPLOC: true");
#else
  logger.Log(1, "PROPLOC: false");
#endif
#ifdef SPDLOG_DEBUG_ON
  logger.Log(1, "SPDLOG_DEBUG_ON: true");
#else
  logger.Log(1, "SPDLOG_DEBUG_ON: false");
#endif
#ifdef NDEBUG
  logger.Log(1, "NDEBUG: true");
#else
  logger.Log(1, "NDEBUG: false");
#endif
#ifdef HAVE_BOOST_IOSTREAMS
  logger.Log(1, "HAVE_BOOST_IOSTREAMS: true");
#else
  logger.Log(1, "HAVE_BOOST_IOSTREAMS: false");
#endif
}

} // end namespace euforia

// Prints stats if we get a ctrl-c
static void sigterm_handler(int /*signal*/) {
  auto end = clk.now();
  TimerDuration dur = (end - start_time);
  if (chk) {
    Statistics st;
    chk->collect_statistics(&st);
    st.Print(logger.out());
  }
  logger.Log(1, "total_time: {:.6f}", dur.count());

  if (SVcompOutput) {
    std::cout << std::endl << "TIMEOUT" << endl;
    std::cout.flush();
    std::exit(EXIT_SUCCESS);
  } else {
    std::cout << "SIGTERM, exiting" << endl;
    std::cout.flush();
    exit(1);
  }
}


//^----------------------------------------------------------------------------^
// Command line options

using namespace llvm;

cl::opt<string> filename(
    cl::Positional,
    cl::desc("<input VMT file>"),
    cl::init("-"));

cl::opt<int> verbosity(
    "v",
    cl::desc("verbosity (0-n)"),
    cl::init(0));

static cl::opt<string, true /* external storage location */> out_dir(
    "out-dir",
    cl::desc("output directory"),
    cl::location(LOG_DIR),
    cl::init(""));

static cl::opt<bool> witness(
    "witness",
    cl::desc("print witness after checking"),
    cl::init(false));
cl::alias witness_a("w", cl::desc("Alias for -witness"), cl::aliasopt(witness));

static cl::opt<bool, true> no_check(
    "no-check",
    cl::desc("Just construct the system, no check"),
    cl::location(euforia_config.no_check),
    cl::init(false));

static cl::opt<int> true_exit_status(
    "true-exit-status",
    cl::desc("number to exit with if property holds"),
    cl::init(EXIT_SUCCESS));

static cl::opt<int> false_exit_status(
    "false-exit-status",
    cl::desc("number to exit with if property doesn't hold"),
    cl::init(EXIT_SUCCESS));

static cl::opt<bool, true> no_abstract_arrays(
    "no-abstract-arrays",
    cl::desc("Do not abstract array theory terms"),
    cl::location(euforia_config.no_abstract_arrays),
    cl::init(false));

static cl::opt<bool, true> abstract_selects_freshly(
    "abstract-selects-freshly",
    cl::desc("Abstract array selects as fresh 0-arity terms (not functions)"),
    cl::location(euforia_config.abstract_array_select_fresh),
    cl::init(false));

static cl::opt<bool, true> use_layered_refinement_queries(
    "use-layered-refinement-queries",
    cl::desc("Try middle-abstraction layerings of refinement queries"),
    cl::location(euforia_config.use_layered_refinement_queries),
    cl::init(false));

static cl::opt<bool, true> use_refinement_queries_without_t(
    "use-refinement-queries-without-t",
    cl::desc("Try step-refinement queries without T first"),
    cl::location(euforia_config.refinement_queries_without_t),
    cl::init(false));

static cl::opt<bool, true> use_only_bmc_refinement(
    "use-only-bmc-refinement",
    cl::desc("Use BMC exclusively for refinement"),
    cl::location(euforia_config.use_only_bmc_refinement),
    cl::init(false));

static cl::opt<bool, true> use_one_shot_bmc_refinement(
    "use-one-shot-bmc-refinement",
    cl::desc( "Use newer one-shot BMC query for BMC refinement"),
    cl::location(euforia_config.use_one_shot_bmc_refinement),
    cl::init(true));

static cl::opt<bool, true> one_shot_bmc_slicing(
    "one-shot-bmc-slicing",
    cl::desc("Slice T during one-shot BMC refinement"),
    cl::location(euforia_config.use_osbmc_slicing),
    cl::init(false));

static cl::opt<bool, true> dump_queries(
    "dump-queries",
    cl::desc( "Dump one step queries in SMT2 format (solveRelativeXXX.smt2)"),
    cl::location(euforia_config.dump_abstract_queries),
    cl::init(false));

static cl::opt<bool, true> verify_invariant(
    "verify-invariant",
    cl::desc( "Check that the invariant is inductive at bit level"),
    cl::location(euforia_config.verify_invariant),
    cl::init(false));

static cl::opt<bool, true> minimize_invariant(
    "minimize-invariant",
    cl::desc( "Minimize the inductive invariant"),
    cl::location(euforia_config.minimize_invariant),
    cl::init(false));

static cl::opt<bool, true> running_stats(
    "running-stats",
    cl::desc( "Print running stats"),
    cl::location(euforia_config.running_stats),
    cl::init(false));
cl::alias running_stats_a(
    "x", cl::desc("Alias for -running-stats"), cl::aliasopt(running_stats));

static cl::opt<bool, true> sort_cubes(
    "sort-cubes",
    cl::desc( "Sort proof obligation cubes for Maximum Determinism"),
    cl::location(euforia_config.sort_cubes),
    cl::init(false));

static cl::opt<bool, true> check_for_redundant_lemmas(
    "check-for-redundant-lemmas",
    cl::desc( "Debug checks for redundant lemmas"),
    cl::location(euforia_config.check_for_redundant_lemmas),
    cl::init(false));

static cl::opt<bool, true> enable_creduce(
    "creduce",
    cl::desc( "Enables extra checks to improve creduce results"),
    cl::location(euforia_config.creduce),
    cl::init(false));

namespace {
// Namespace so z3 and boolector don't collide.

// These variable names are used as the option names on the command line, like
// --refinement-solver=boolector instead of --refinement-solver=kBoolector.
static auto z3 = config::kZ3;
static auto boolector = config::kBoolector;
static cl::opt<config::SupportedSolver, true> refinement_solver(
    "refinement-solver",
    cl::desc("which refinement solver to use:"),
    cl::values(
        clEnumVal(z3, "Z3"),
        clEnumVal(boolector, "Boolector")),
    cl::location(euforia_config.refinement_solver),
    cl::init(z3));
} // namespace

static void PrintVersion(raw_ostream& ) {
  unsigned z3_major, z3_minor, z3_build_num, z3_rev_num;
  Z3_get_version (&z3_major, &z3_minor, &z3_build_num, &z3_rev_num);
  fmt::print("euforia {}.{}\n", euforia_major_version,
             euforia_minor_version);
  fmt::print("commit {}, branch {}, tag {}\n",
             git_version, git_branch, git_tag);
  fmt::print("c++ {}\n", __cplusplus);
  fmt::print("compiled with Z3 version {}.{} [build {}, revision {}]\n",
             z3_major, z3_minor, z3_build_num, z3_rev_num);
}

//^----------------------------------------------------------------------------^
// Entry point

int main(int argc, char *const *argv) {
  TimerDuration before_check_duration(0);
  ScopedTimeKeeper before_check_keeper(&before_check_duration);
  //dup2(1, 2); /* send stderr to stdout */
  std::signal(SIGTERM, sigterm_handler);
  std::signal(SIGINT, sigterm_handler);

  //  setenv("BTORAPITRACE", "/tmp/btorapitrace", 0);

  cl::SetVersionPrinter(PrintVersion);
  cl::ParseCommandLineOptions(argc, argv);
  // use -print-all-options on command line
  cl::PrintOptionValues();
  logger.set_level(verbosity);

  PrintFeatures();
  logger.Log(1, "witness: {}", witness);
  logger.Log(1, "{}", euforia_config);

  start_time = clk.now();

  if (euforia_config.dump_abstract_queries) {
    if (LOG_DIR.empty()) {
      fmt::print(cerr, "dumping requested but no --out-dir so no place to dump");
      exit(EXIT_FAILURE);
    }
  }


  // create LOG_DIR if it doesn't exist
  if (!LOG_DIR.empty()) {
    if (auto dirError = fs::create_directories(LOG_DIR)) {
      cerr << "error creating out directories: " << dirError.message();
      exit(EXIT_FAILURE);
    }
    logger.set_mirror_file(LOG_DIR + "/euforia.log");
  }

  //spdlog::get("euforia")->set_level(spdlog::level::level_enum::debug);
  //spdlog::get("*preimg")->set_level(spdlog::level::level_enum::debug);
  //spdlog::get("*gen")->set_level(spdlog::level::level_enum::debug );
  //spdlog::get("*refine")->set_level(spdlog::level::level_enum::debug );

  // nlogger.Enable("generalize");
  // nlogger.Enable("queries");

#ifdef EXPENSIVECHECKS
  logger.Log(0, "warning: expensive checks are enabled");
#endif

  logger.Log(1, "prepare for descent");

  int exit_status;
  wordexp_t wp;
  int failure = wordexp(filename.c_str(), &wp, 0);
  if (failure) {
    cerr << "Unable to expand target filename" << endl;
    exit(EXIT_FAILURE);
  }
  filename = string(wp.we_wordv[0]);
  logger.Log(1, "target: {}", filename);

  // Z3_enable_trace("dl");
  // Z3_enable_trace("dl_rule");
  // Z3_enable_trace("spacer");
  //Z3_set_ast_print_mode(ctx, Z3_PRINT_SMTLIB_FULL);
  z3::set_param("pp.max_width", 150);
  z3::set_param("pp.max_ribbon", 150);
  z3::set_param("auto_config", false);
  z3::set_param("model", true);
  z3::set_param("proof", false);
  z3::set_param("unsat_core", true);
  //Z3_enable_trace("model_evaluator");

  msat_config mcfg = msat_create_config();
  msat_env menv = msat_create_env(mcfg);
  MathsatEnvDeleter del_menv(menv);
  msat_destroy_config(mcfg);

  struct stat buffer;
  if (stat(filename.c_str(), &buffer) != 0) {
    auto error = strerror(errno);
    fmt::print(cerr, "Error loading target: {}\n", error);
    exit(EXIT_FAILURE);
  }

  // try {
  string filebuf = ReadFile(filename);

  logger.Log(1, "parsing vmt file");
  auto ast = euforia::vmt::VmtParseStr(filebuf, menv);
  logger.Log(1, "building concrete transition system");
  vmt::ConcreteVmtTransitionSystem ts(ast, ctx);
  Statistics sst;
  if (euforia_config.creduce) CreduceRegulateTransitionSystem(ts);
  ts.Prepare();
  logger.Log(4, "concrete transition system:\n{}", ts);
  if (!LOG_DIR.empty()) {
    // Dump model checking instance for easy experimentation at the SMT level.
    z3::expr_vector v(ctx);
    v.push_back(ctx.bool_const(".init") == ts.init_state());
    v.push_back(ctx.bool_const(".trans") == ts.trans());
    v.push_back(ctx.bool_const(".property") == ts.property());
    v.push_back(ctx.bool_const(".property-next") == ts.prime(ts.property()));
    v.push_back(ctx.bool_const(".not-property-next") ==
                ts.prime(expr_not(ts.property())));
    ofstream f(LOG_DIR + "/citp-concrete-check-instance.smt2");
    if (f.is_open()) {
      auto s = ToSmt2WithAssumps(v, ExprSet(), filename, ts.solver_logic());
      f << s;
    }
  }
  logger.Log(1, "abstracting concrete transition system");
  vmt::AbstractVmtTransitionSystem ats(ts, euforia_config);
  ts.collect_static_statistics(&sst);
  ts.TransitionSystem::collect_static_statistics(&sst);
  ats.collect_static_statistics(&sst);
  if (logger.ShouldLog(1))
    sst.Print(logger.out());
  logger.Log(4, "abstract transition system:\n{}", ats);
  chk = std::make_unique<AbstractChecker>(ats);
  // chk->set_abstraction_refinement(false);
  auto before_check_time = before_check_keeper.get();
  logger.Log(1, "before_check_time: {} - time spent before running the actual check",
             before_check_time.count());
  auto check_start_time = clk.now();
  if (euforia_config.no_check) {
    return EXIT_SUCCESS;
  }
  bool has_cx = chk->Run();
  chrono::duration<double> check_time = clk.now() - check_start_time;
  std::unique_ptr<Counterexample> cx;
  if (has_cx) {
    if (witness) {
      cx = chk->TakeCounterexample();
      cx->print(std::cout);
    }
    exit_status = false_exit_status;
    fmt::print("false(unreach-call)\n");
  } else {
    if (witness) {
      auto q = chk->concrete_invariant_query();
      // q is [invariant, !invariant']
      assert(q.size() == 2);
      auto print_q = [&](std::ostream& os) {
        fmt::print(os, "(declare-fun .invariant () Bool)\n");
        fmt::print(os, "(assert {})\n", ctx.bool_const(".invariant") == q[0]);
        fmt::print(os, "(declare-fun .not-invariant-next () Bool)\n");
        fmt::print(os, "(assert {})\n", ctx.bool_const(".not-invariant-next") == q[1]);
      };

      fmt::print("begin concrete invariant\n");
      print_q(std::cout);
      fmt::print("end concrete invariant\n");
      if (!LOG_DIR.empty()) {
        ofstream f(LOG_DIR + "/invariant.smt2");
        if (f.is_open()) {
          fmt::print(f, ";; put this in concrete check instance file\n");
          print_q(f);

          fmt::print(f, ";; checks Init => Inv\n");
          fmt::print(f, "; (assert (not .invariant))\n");
          fmt::print(f, "; (assert .init)\n");

          fmt::print(f, ";; checks Inv & T => Inv'\n");
          fmt::print(f, "; (assert .invariant)\n");
          fmt::print(f, "; (assert .trans)\n");
          fmt::print(f, "; (assert .not-invariant-next)\n");

          fmt::print(f, ";; checks Inv => P\n");
          fmt::print(f, "; (assert .invariant)\n");
          fmt::print(f, "; (assert (not .property))\n");
          fmt::print(f, "; (check-sat)\n");
        }
      }

    }
    exit_status = true_exit_status;
    fmt::print("true(unreach-call)\n");
  }
  logger.Log(1, "total_time: {:.6f}", check_time.count());
  Statistics st;
  chk->collect_statistics(&st);
  ats.collect_statistics(&st);
  if (logger.ShouldLog(1))
    st.Print(logger.out());

  // } catch (const z3::exception& e) {
  //   fmt::print(std::cerr, "FOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO");
  //   fmt::print(std::cerr, "z3 exception:\n");
  //   fmt::print(std::cerr, "{}", e.msg());
  //   std::flush(std::cerr);
  //   throw;
  // }
  return exit_status;
}
