// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/z3_solver.h"

#include <boost/tuple/tuple.hpp>
#include <boost/iterator/iterator_facade.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/iterator/zip_iterator.hpp>
#include <cassert>

#include "checker_types.h"
#include "supp/pool_storage.h"
#include "supp/std_supp.h"

using namespace std;

namespace euforia {

util::pool_storage_std<string> alloc_str;

//^----------------------------------------------------------------------------^
// Z3Assignment

z3::expr Z3Assignment::as_constraint(const z3::expr& var) const {
  if (var_.is_array()) {
    z3::expr_vector conjuncts(var_.ctx());
    auto e = val_;
    while (e.is_app() && e.decl().decl_kind() == Z3_OP_STORE) {
      auto index = e.arg(1);
      auto value = e.arg(2);
      conjuncts.push_back(z3::select(var, index) == value);
      e = e.arg(0);
    }
    return expr_mk_and(conjuncts);
  }

  return Assignment::as_constraint(var);
}

//^----------------------------------------------------------------------------^
// Z3Model


void Z3Model::collect_statistics(Statistics *st) const {
#define upd(stat) st->Update(#stat, stat ## _)
  upd(num_bool_evals); //: {}\n", num_bool_evals_);
  upd(num_uninterpreted_evals); //: {}\n", num_uninterpreted_evals_);
  upd(num_unknown_evals); //: {}\n", num_unknown_evals_);
  int64_t num_evals_ = num_bool_evals_ + num_uninterpreted_evals_ +
      num_unknown_evals_;
  upd(num_evals);
#undef upd
}

z3::expr Z3Model::Eval(const z3::expr& e, bool c) {
  if (e.is_bool())
    ++num_bool_evals_;
  else if (IsUninterp(e))
    ++num_uninterpreted_evals_;
  else
    ++num_unknown_evals_;
  // XXX eval($K_5) is being called which should be a no-op but might cause Z3
  // to do work, i.e., to evaluate it to the equivalence class it was assigned
  // to. also, if I channge that it might break my partition model. That stuff
  // is old and might need to change...
  return model_.eval(e, c);
}

std::unique_ptr<Assignment> Z3Model::assignment(z3::expr var) {
  return make_unique<Z3Assignment>(var, Eval(var, false));
}

pp::DocPtr Z3Model::Pp() const {
  using namespace pp;

  // Convers pair of decl / interpreteation (either expr or func_interp) to doc
  auto pair_to_const_interp_doc = make_function_object([](auto p) -> DocPtr {
    return nest_used(group(append(
                {Pprint(boost::get<0>(p).name().str()), line(),
                text("="), line(), Pprint(boost::get<1>(p))})));
  });
  auto pair_to_func_interp_doc = make_function_object([](auto p) -> DocPtr {
    return nest_used(group(append(
                {Pprint(boost::get<0>(p).name().str()),
                nest(2, append(newline(), Pprint(boost::get<1>(p))))})));
  });

  auto banner = append(
      {text("Z3Model of size "),
      Pprint(model_.size()), text(" with "),
      Pprint(model_.num_consts()), text(" constants"),
      text(" and "),
      Pprint(model_.num_funcs()), text(" functions"),
      newline()});

  // Prints decls themselves first
  auto sep = line();
  auto const_decls = group(
      separate(ModelConstDeclIterator(model_),
               ModelConstDeclIterator(model_, model_.num_consts()), sep));
  auto func_decls = group(
      separate(ModelFuncDeclIterator(model_),
               ModelFuncDeclIterator(model_, model_.num_funcs()), sep));

  // Prints values second
  auto const_begin = boost::make_transform_iterator(
      boost::make_zip_iterator(
          boost::make_tuple(ModelConstDeclIterator(model_),
                            ModelConstInterpIterator(model_))),
      pair_to_const_interp_doc);
  auto const_end = boost::make_transform_iterator(
      boost::make_zip_iterator(
          boost::make_tuple(
              ModelConstDeclIterator(model_, model_.num_consts()),
              ModelConstInterpIterator(model_, model_.num_consts()))),
      pair_to_const_interp_doc);
  auto const_interps = group(separate(const_begin, const_end, sep));

  auto func_begin = boost::make_transform_iterator(
      boost::make_zip_iterator(
          boost::make_tuple(ModelFuncDeclIterator(model_),
                            ModelFuncInterpIterator(model_))),
      pair_to_func_interp_doc);
  auto func_end = boost::make_transform_iterator(
      boost::make_zip_iterator(
          boost::make_tuple(
              ModelFuncDeclIterator(model_, model_.num_funcs()),
              ModelFuncInterpIterator(model_, model_.num_funcs()))),
      pair_to_func_interp_doc);
  auto func_interps = group(separate(func_begin, func_end, newline()));

  return append(
      {banner,
      Pprint(model_.num_consts()), text(" const_decls"),
      nest(4, append(newline(), const_decls)), newline(),
      Pprint(model_.num_funcs()), text(" func_decls"),
      nest(4, append(newline(), func_decls)), newline(),
      text("const_interps"), nest(4, append(newline(), const_interps)),
      newline(),
      text("func_interps"), nest(4, append(newline(), func_interps))});
}

//*----------------------------------------------------------------------------*
// Z3Solver
Z3Solver::Z3Solver(z3::context& ctx) : solver_(ctx) {}

Z3Solver::Z3Solver(z3::solver s) : solver_(s) {}

Z3Solver::Z3Solver(z3::context& ctx, const char *logic) : solver_(ctx, logic) {
  assert(logic);
}

std::string ToSmt2WithAssumps(const z3::expr_vector& assertions_in,
                              const ExprSet& assumps,
                              const std::string& name,
                              const std::string& logic) {
  const char *status = "unknown";
  z3::expr_vector assertions(assertions_in);
  for (const auto& assump : assumps)
    assertions.push_back(assump);
  z3::array<Z3_ast> es(assertions);
  Z3_ast const* fmls = es.ptr();
  Z3_ast fml = 0;
  unsigned sz = es.size();
  if (sz > 0) {
    --sz;
    fml = fmls[sz];
  }
  else {
    fml = assertions.ctx().bool_val(true);
  }
  return std::string(Z3_benchmark_to_smtlib_string(
          assertions.ctx(), name.c_str(), logic.c_str(), status, "", sz, fmls,
          fml));
}

void Z3Solver::Add(const z3::expr& e) {
  solver_.add(e);
}

void Z3Solver::Push() {
  solver_.push();
}

void Z3Solver::Pop() {
  solver_.pop();
}

// All versions of check should be routed through this function
CheckResult Z3Solver::Check(const size_t n, const z3::expr* assumptions) {
  auto z3_result = ProcessCheck(solver_.check(
          static_cast<unsigned>(n),
          const_cast<z3::expr*>(assumptions)));
  return TranslateResult(z3_result);
}

std::shared_ptr<Model> Z3Solver::get_model() {
  return std::make_shared<Z3Model>(solver_.get_model());
}

z3::check_result Z3Solver::ProcessCheck(const z3::check_result& r) {
  ++num_solve_calls_;
  if (r == z3::sat) {
    ++num_solve_sat_calls_;
  } else if (r == z3::unsat) {
    ++num_solve_unsat_calls_;
  }
  return r;
}

z3::expr_vector Z3Solver::unsat_core_reasons() {
  z3::expr_vector reasons(ctx());
  auto core = unsat_core();
  for (const auto& b : core) {
    reasons.push_back(GetTracked(b, b));
  }
  return reasons;
}


void Z3Solver::DumpBenchmark(
    std::ostream& os, size_t n, const z3::expr* assumptions) {
  fmt::print(os, "; dumped by Z3Solver\n");
  if (n) {
    z3::solver copy(solver_.ctx());
    for (const auto& a : solver_.assertions()) {
      copy.add(a);
    }
    for (auto it = assumptions, ie = assumptions + n; it != ie; ++it) {
      copy.add(*it);
    }
    os << copy.to_smt2();
  } else {
    auto str = solver_.to_smt2();
    os << str;
  }
}

  void Z3Solver::printAssertions(int log_level) const {
    if (logger.ShouldLog(log_level)) {
      logger.Log(log_level, "assertions:");
      auto assertions = solver_.assertions();
      for (size_t i = 0; i < assertions.size(); i++) {
        logger.Log(log_level, "{}", assertions[i]);
      }
    }
  }


void Z3Solver::collect_statistics(Statistics *st) const {
  Solver::collect_statistics(st);
  auto solver_stats = solver_.statistics();
  for (unsigned i = 0; i < solver_stats.size(); i++) {
    auto& key = alloc_str("z3 " + solver_stats.key(i));
    if (solver_stats.is_uint(i)) {
      st->Update(key.c_str(), static_cast<int64_t>(solver_stats.uint_value(i)));
    } else if (solver_stats.is_double(i)) {
      st->Update(key.c_str(), solver_stats.double_value(i));
    }
  }
}

}

