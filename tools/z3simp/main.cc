// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno


#include <boost/iterator/transform_iterator.hpp>
#include <boost/program_options.hpp>
#include <boost/range.hpp>
#include <boost/range/adaptor/indexed.hpp>
#include <boost/range/combine.hpp>
#include <fmt/format.h>
#include <fmt/ostream.h>
#include <fstream>
#include <gmpxx.h>
#include <map>
#include <set>
#include <sstream>
#include <vector>
#include <z3++.h>

using namespace z3;

class Logger {
  int level_;
  uint64_t count_;
  std::ofstream mirror_file_;

 public:
  Logger() : level_(0), count_(0) {}

  void set_level(int level) { level_ = level; }

  bool ShouldLog(int level) { return level <= level_; }

  void set_mirror_file(std::string filename) {
    mirror_file_ = std::ofstream(filename);
  }

  template <typename... Args> void Log(int level, const char *fmt,
                                       const Args&... args) {
    if (ShouldLog(level)) {
      auto fmt_msg = [&](std::ostream& os) {
        fmt::print(os, fmt, std::forward<const Args>(args)...);
        fmt::print(os, "\n");
      };
      //fmt::print(std::cerr, "[{:06d}] ", count_);
      fmt_msg(std::cerr);
      if (mirror_file_.is_open())
        fmt_msg(mirror_file_);
      ++count_;
    }
  }
  
  template <typename... Args> void LogOpenFold(int level, const char *fmt,
                                               const Args&... args) {
    if (ShouldLog(level)) {
      //fmt::print(std::cerr, "[{:06d}] ", count_);
      auto fmt_msg = [&](std::ostream& os) {
        fmt::print(os, fmt, std::forward<const Args>(args)...);
        fmt::print(os, "{{{{{{");
        fmt::print(os, "\n");
      };
      fmt_msg(std::cerr);
      if (mirror_file_.is_open())
        fmt_msg(mirror_file_);
      ++count_;
    }
  }
  
  template <typename... Args> void LogCloseFold(int level, const char *fmt,
                                                const Args&... args) {
    if (ShouldLog(level)) {
      //fmt::print(std::cerr, "[{:06d}] ", count_);
      auto fmt_msg = [&](std::ostream& os) {
        fmt::print(os, fmt, std::forward<const Args>(args)...);
        fmt::print(os, "}}}}}}");
        fmt::print(os, "\n");
      };
      fmt_msg(std::cerr);
      if (mirror_file_.is_open())
        fmt_msg(mirror_file_);
      ++count_;
    }
  }

  void Log(int level, const char *msg) {
    if (ShouldLog(level)) {
      //fmt::print(std::cerr, "[{:06d}] ", count_);
      auto fmt_msg = [&](std::ostream& os) {
        fmt::print(os, msg);
        fmt::print(os, "\n");
      };
      fmt_msg(std::cerr);
      if (mirror_file_.is_open())
        fmt_msg(mirror_file_);
      ++count_;
    }
  }
};

static Logger logger;

//^----------------------------------------------------------------------------^
//
namespace po = boost::program_options;

po::options_description desc("options");

int main(int argc, char **argv) {
  // option parsing
  desc.add_options()
      ("help,h", "help")
      ("v", po::value<int>()->default_value(0), "set log level")
      ("smt2", po::value<bool>()->default_value(true),
       "if on, prints output as smt2 benchmark")
      ("check", po::value<bool>()->default_value(false),
       "if on, performs a check-sat after simplification")
      ("filename", po::value<std::string>(), "SMT2 file to convert");
  po::positional_options_description pd;
  pd.add("filename", -1);
  po::variables_map opt_map;
  po::store(po::command_line_parser(argc, argv).
            options(desc).positional(pd).run(), opt_map);
  po::notify(opt_map);

  if (!opt_map.count("filename")) {
    fmt::print(std::cerr, "error: missing filename\n");
  }
  if (opt_map.count("help") || !opt_map.count("filename")) {
    fmt::print(std::cout, "usage:\n{} filename\n{}\n", argv[0], desc);
    return EXIT_FAILURE;
  }

  logger.set_level(opt_map["v"].as<int>());

  auto filename = opt_map["filename"].as<std::string>();
  context ctx;
    
  // Reads file into buffer because we are lazily copying code
  std::string filebuf;
  {
    std::ifstream fin(filename);
    if (!fin.is_open()) {
      fmt::print(std::cerr, "error: could not open file: {}\n", filename);
      return EXIT_FAILURE;
    }
    std::stringstream sstr;
    sstr << fin.rdbuf();
    filebuf = sstr.str();
  }
  expr_vector things(ctx);
  try {
    // Parse file into Z3 representation
    things = ctx.parse_string(filebuf.c_str());
  } catch (z3::exception& e) {
    fmt::print(std::cerr, "error: {}\n", e.msg());
    return EXIT_FAILURE;
  }
  logger.Log(1, "parsed");

  // Build tactic lib
  tactic ctx_solver_simplify_constraints = tactic(ctx, "ctx-solver-simplify");
  tactic simplify_constraints = tactic(ctx, "simplify");
  tactic propagate_constants(ctx, "propagate-values");
  tactic solve_eqs(ctx, "solve-eqs");
  tactic ctx_simplify_constraints = tactic(ctx, "ctx-simplify");
  tactic der(ctx, "der"); // destructive equality resolution
  tactic reduce_bv_size(ctx, "reduce-bv-size");
  tactic sat_preprocess(ctx, "sat-preprocess"); // warning, introduces extra vars
  tactic propagate_bv_bounds_new(ctx, "propagate-bv-bounds-new");
  tactic injectivity(ctx, "injectivity");
  tactic bvarray2uf(ctx, "bvarray2uf"); // does not instantiate any array axioms
  tactic propagate_ineqs(ctx, "propagate-ineqs");
  tactic unit_subsume_simplify(ctx, "unit-subsume-simplify");
  tactic ackermannize_bv(ctx, "ackermannize_bv");
  
  // If I want to operate tactics on the Boolean skeleton, see the goal2sat
  // tactic.

  // Adds the assertions found in the file as goals
  goal g(ctx);
  for (unsigned i = 0; i < things.size(); i++) {
    g.add(things[i]);
  }
  logger.Log(1, "created goal");

  // Runs the simplifier and outputs the result
  // a & b & c will run a, then b on a's subgoals, then c on b's subgoals.
  auto simplifier = //repeat (
      simplify_constraints & 
      propagate_constants & 
      solve_eqs & // will do (and bool-1 (or bool-1 <c>)) = <c>
      // unit_subsume_simplify & simplify_constraints &  // unit_subsume_simplify is the slowest of these, be careful
      ctx_simplify_constraints & // might generate new units for solve_eqs
      solve_eqs &
      // ctx_solver_simplify_constraints &
      simplify_constraints;
  auto output = simplifier(g);
  fmt::print(std::cout, "; z3simp results\n");
  fmt::print(std::cout, "; {} subgoals\n", output.size());
  solver s(ctx);
  for (unsigned i = 0; i < output.size(); i++) {
    fmt::print(std::cout, "; subgoal {} has {} children\n", i+1,
               output[i].size());
      s.add(output[i].as_expr());
    if (!opt_map["smt2"].as<bool>()) {
      fmt::print(std::cout, "{}\n", output[i]);
    }
  }
  if (opt_map["smt2"].as<bool>()) {
    fmt::print(std::cout, "{}\n", s.to_smt2());
  }
  if (opt_map["check"].as<bool>()) {
    const auto result = s.check();
    fmt::print(std::cout, "{}\n", result);
    if (check_result::sat == result) {
      model m = s.get_model();
      fmt::print(std::cout, "{}\n", m);
    }
  }
  
  
  return EXIT_SUCCESS;
}
