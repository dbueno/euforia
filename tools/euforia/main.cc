// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include <llvm/Support/FileSystem.h>
#include <string>
#include <unordered_map>
#include <iostream>
#include <cassert>
#include <regex>
#include <csignal>
#include <chrono>
#include <mathsat.h>
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
static bool witness = false;
static bool SVcompOutput = true;
static int true_exit_status = EXIT_SUCCESS, false_exit_status = EXIT_SUCCESS;
unique_ptr<AbstractChecker> chk;

namespace euforia {

// Storage for configuration
config::Config euforia_config;
extern unsigned euforia_major_version;
extern unsigned euforia_minor_version;

static void PrintFeatures() {
  unsigned z3Major, z3Minor, z3BuildNumber, z3RevisionNumber;
  Z3_get_version (&z3Major, &z3Minor, &z3BuildNumber, &z3RevisionNumber);

  logger.Log(1, "EUForia version {}.{}", euforia_major_version,
             euforia_minor_version);
  logger.Log(1, "commit {}, branch {}, tag {}",
             git_version, git_branch, git_tag);
  logger.Log(1, "c++ {}", __cplusplus);
  logger.Log(1, "compiled with Z3 version {}.{} [build {}, revision {}]",
             z3Major, z3Minor, z3BuildNumber, z3RevisionNumber);
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
  
  
static struct option longOptions[] = {
  /* These options set a flag. */
  {"verbose", required_argument, 0, 'v'},
  {"out-dir", required_argument, 0, 0},
  {"witness", no_argument, 0, 'w'},
  {"no-check", no_argument, &euforia_config.no_check, 1},
  {"true-exit-status", required_argument, 0, 0},
  {"false-exit-status", required_argument, 0, 0},
  {"no-abstract-arrays", no_argument, &euforia_config.no_abstract_arrays, 1},
  {"abstract-selects-freshly", no_argument, &euforia_config.abstract_array_select_fresh, 1},
  {"use-layered-refinement-queries", no_argument,
    &euforia_config.use_layered_refinement_queries, 1},
  {"use-refinement-queries-without-t", no_argument,
    &euforia_config.refinement_queries_without_t, 1},
  {"use-only-bmc-refinement", no_argument,
    &euforia_config.use_only_bmc_refinement, 1},
  {"use-one-shot-bmc-refinement", no_argument,
    &euforia_config.use_one_shot_bmc_refinement, 1},
  {"one-shot-bmc-slicing", no_argument,
    &euforia_config.use_osbmc_slicing, 1},
  {"dump-queries", no_argument,
    &euforia_config.dump_abstract_queries, 1},
  {"verify-invariant", no_argument,
    &euforia_config.verify_invariant, 1},
  {"minimize-invariant", no_argument, &euforia_config.minimize_invariant, 1},
  {"running-stats", no_argument, 0, 'x'},
  {"use-tseitin", no_argument, &euforia_config.use_tseitin, 1},
  {"sort-cubes", no_argument, &euforia_config.sort_cubes, 1},
  {"refinement-solver", required_argument, 0, 0},
  {"check-for-redundant-lemmas", no_argument,
    &euforia_config.check_for_redundant_lemmas, 1},
  {"creduce", no_argument, &euforia_config.creduce, 1},
  /* These options don’t set a flag.
     We distinguish them by their indices. */
  {"help",     no_argument,       0, 'h'},
  {0, 0, 0, 0}
};

static const char *descr[] = {
  "Set verbosity level (1-n)",
  "Use the given path for output files",
  "Print the invariant/counterexample",
  "Just construct the system, no check",
  "If given, EUForia will exit with given exit code if property holds",
  "If given, EUForia will exit with given exit code if property doesn't hold",
  "Leave array theory intact at abstract level",
  "Abstract array selects as fresh 0-arity terms (not functions)",
  "Try middle-abstraction layerings of refinement queries",
  "Try step-refinement queries without T first",
  "Use BMC exclusively for refinement",
  "Use newer one-shot BMC query for BMC refinement",
  "Slice T during one-shot BMC refinement",
  "Dump one step queries in SMT2 format (solveRelativeXXX.smt2)",
  "Check that the invariant is inductive at bit level",
  "Minimize the inductive invariant",
  "Print running stats",
  "Use tseitin transformation to speed up eval()",
  "Sort proof obligation cubes for maximum determinism",
  "Choice of refinement solver: boolector or z3",
  "Debug checks for redundant lemmas",
  "Enables extra checks to improve creduce results",
  "This help",
  nullptr
};

int main(int argc, char *const *argv) {
  TimerDuration before_check_duration(0);
  ScopedTimeKeeper before_check_keeper(&before_check_duration);
  //dup2(1, 2); /* send stderr to stdout */
  std::signal(SIGTERM, sigterm_handler);
  std::signal(SIGINT, sigterm_handler);

  // Initializes EUForia's default configuration
  // default-initialize everything except...
  euforia_config.use_one_shot_bmc_refinement = 1;
  euforia_config.refinement_solver = config::kZ3;

  // pretty printing width
  pp::best_width = 160;

  //  setenv("BTORAPITRACE", "/tmp/btorapitrace", 0);

  while (true) {
    /* getopt_long stores the option index here. */
    int optionIndex = 0;
    int c = getopt_long(argc, argv, "v:wIhx", longOptions, &optionIndex);
    
    /* Detect the end of the options. */
    if (c == -1)
      break;
    
    auto currOption = string(longOptions[optionIndex].name);

    switch (c) {
      case 0: {
        /* If this option set a flag, do nothing else now. */
        if (longOptions[optionIndex].flag != 0)
          break;

        else if (currOption == "out-dir") {
          LOG_DIR = string(optarg);
        }
        
        else if (currOption == "true-exit-status") {
          true_exit_status = std::stoi(optarg);
        }

        else if (currOption == "false-exit-status") {
          false_exit_status = std::stoi(optarg);
        }

        else if (currOption == "refinement-solver") {
          euforia_config.refinement_solver =
              config::solver_from_string(string(optarg));
        }

        break;
      }

      case 'v': {
        int n = 1;
        n = stoi(optarg);
        logger.set_level(n);
      }
        break;
        
      case 'w':
        witness = true;
        break;

      case 'x':
        euforia_config.running_stats = true;
        break;
        
      case 'h': {
        logger.Log(0, "EUForia version {}.{}", euforia_major_version,
                   euforia_minor_version);
        logger.Log(0, "commit {}, branch {}, tag {}",
                   git_version, git_branch, git_tag);
        printf("%s [options] filename.bc\n", argv[0]);
        printf("available options\n");
        for (int i = 0; longOptions[i].name; i++) {
          struct option *opt = &longOptions[i];
          printf("  ");
          if (opt->val) {
            printf("-%c, ", opt->val);
          }
          printf("--%s", opt->name);
          switch (opt->has_arg) {
            case no_argument:
              break;
            case required_argument:
              printf("=ARG");
              break;
            case optional_argument:
              printf("[=ARG]");
              break;
            default:
              abort();
          }
          printf(": %s\n", descr[i]);
        }
        exit(EXIT_SUCCESS);
        break;
      }
        
      case '?':
        /* getopt_long already printed an error message. */
        exit(EXIT_FAILURE);
        break;
        
      default:
        abort();
    }
  }

  PrintFeatures();
  logger.Log(1, "witness: {}", witness);
  logger.Log(1, "{}", euforia_config);
  
  start_time = clk.now();
  std::string error_msg;
  std::string filename;
  if (optind >= argc) {
    cerr << "Please give a vmt file to analyze" << endl;
    exit(EXIT_FAILURE);
  }

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
  int failure = wordexp(argv[optind], &wp, 0);
  if (failure) {
    cerr << "Unable to expand filename" << endl;
    exit(EXIT_FAILURE);
  }

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

  filename = wp.we_wordv[0];
  logger.Log(1, "target: {}", filename);

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
