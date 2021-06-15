// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "layered_refinement.h"

#include <boost/range/algorithm/copy.hpp>
#include <boost/range/algorithm/transform.hpp>

#include "supp/identity_rewriter.h"

using namespace std;
using namespace euforia;

namespace euforia {

// Uses name as the basis for the UF name. e is the concrete expression for
// which you're creating a UF application.
z3::expr Arrays2Uf::AbstractUfIntParams(
    const std::string& name, const z3::expr& e,
    std::function<z3::expr(const z3::expr_vector&)> /*conc_decl*/) {
  // logger.Log(6, "original term: {}", e);
  auto e_decl = e.decl();
  stringstream name_stream;
  name_stream << name;
  for (unsigned i = 0; i < e_decl.arity(); i++) {
    auto sort_name = SortName(e_decl.domain(i));
    name_stream << "_" << sort_name;
  }
  name_stream << "_" << SortName(e_decl.range());

  z3::expr_vector args(e.ctx());
  z3::sort_vector sorts(e.ctx());
  auto ret_sort = e_decl.range();
  for (unsigned i = 0; i < e_decl.arity(); i++) {
    args.push_back(Arg(e, i));
    sorts.push_back(Arg(e, i).get_sort());
    // logger.Log(6, "arg {}: {}, sort: {}", i, args[args.size()-1],
    //            sorts[sorts.size()-1]);
  }
  // logger.Log(6, "ret_sort: {}", ret_sort);

  auto f = e.ctx().function(name_stream.str().c_str(), sorts, ret_sort);
  // logger.Log(6, "f: {}", f);
  auto term = f(args);
  // logger.Log(6, "new term: {}", term);
  return term;
}

//^----------------------------------------------------------------------------^

z3::expr_vector Arrays2Fresh::operator()(const z3::expr_vector& es) {
  z3::expr_vector out(ctx_);
  boost::transform(
      es, ExprVectorInserter(out), [&](auto&& e) { return (*this)(e); });
  return out;
}
  

z3::expr Arrays2Fresh::visitExpr(const z3::expr& e) {
  if (e.get_sort().is_array()) {
    num_arrays_++;
  }
  auto rw = make_identity_rewriter(NewArgsExprVector(e));
  return rw(e);
}


z3::expr Arrays2Fresh::visitUNINTERPRETED(const z3::expr& e) {
  stringstream name_str;
  if (e.is_array()) {
    fmt::print(name_str, "arr2bv-{}", unique_counter_++);
    return e.ctx().bv_const(name_str.str().c_str(),
                            e.get_sort().array_range().bv_size());
  }
  return e.decl()(NewArgsExprVector(e));
}


z3::expr Arrays2Fresh::visitSTORE(const z3::expr& e) {
  stringstream name_str;
  assert(e.num_args()==3);
  std::function<z3::expr(const z3::expr_vector&)> decl =
      [](const z3::expr_vector& args) {
        assert(args.size() == 3);
        return z3::store(args[0], args[1], args[2]);
      };
  fmt::print(name_str, "store2bv-{}", unique_counter_++);
  return e.ctx().bv_const(name_str.str().c_str(),
                          e.get_sort().array_range().bv_size());
}


z3::expr Arrays2Fresh::visitSELECT(const z3::expr& e) {
  stringstream name_str;
  assert(e.num_args()==2);
  std::function<z3::expr(const z3::expr_vector&)> decl =
      [](const z3::expr_vector& args) {
        assert(args.size() == 2);
        return z3::select(args[0], args[1]);
      };
  fmt::print(name_str, "select2bv-{}", unique_counter_++);
  return e.ctx().bv_const(name_str.str().c_str(),
                          e.get_sort().bv_size());
}


z3::expr Arrays2Fresh::visitCONST_ARRAY(const z3::expr& e) {
  stringstream name_str;
  std::function<z3::expr(const z3::expr_vector&)> decl =
      [e](const z3::expr_vector& args) {
        // XXX this doesn't handle the case where abstract_arrays_ is false
        assert(args.size() == 2);
        auto sort = e.get_sort().array_domain();
        return z3::const_array(sort, args[1]);
      };
  fmt::print(name_str, "constarr2bv-{}", unique_counter_++);
  return e.ctx().bv_const(name_str.str().c_str(),
                          e.get_sort().array_range().bv_size());
}

// Uses name as the basis for the UF name. e is the concrete expression for
// which you're creating a UF application.
z3::expr Arrays2Fresh::AbstractUfIntParams(
    const std::string& name, const z3::expr& e,
    std::function<z3::expr(const z3::expr_vector&)> /*conc_decl*/) {
  // logger.Log(6, "original term: {}", e);
  auto e_decl = e.decl();
  stringstream name_stream;
  name_stream << name;
  for (unsigned i = 0; i < e_decl.arity(); i++) {
    // auto sort_name = SortName(e_decl.domain(i));
    name_stream << unique_counter_++;//"_" << name;
  }
  name_stream << "_" << SortName(e_decl.range());

  z3::expr_vector args(e.ctx());
  z3::sort_vector sorts(e.ctx());
  auto ret_sort = (e_decl.range());
  // This code is specific to int parameters. If you have other types, you're
  // out of luck.
#if 0
  auto num_parameters = Z3_get_decl_num_parameters(e.ctx(), e.decl());
  const int param_width = 32; // i decided this arbitrarily
  for (unsigned i = 0; i < num_parameters; i++) {
    auto p = Z3_get_decl_int_parameter(e.ctx(), e.decl(), i);
    auto p_bv = e.ctx().bv_val(p, param_width);
    auto p_abs = visitBNUM(p_bv);
    args.push_back(p_abs);
    sorts.push_back((p_bv.get_sort()));
    logger.Log(6, "arg {}: {}, sort: {}", i, args[args.size()-1],
               sorts[sorts.size()-1]);
  }
#endif
  // for (unsigned i = 0; i < e_decl.arity(); i++) {
  //   args.push_back(Arg(e, i));
  //   sorts.push_back(Arg(e, i).get_sort());
  //   logger.Log(6, "arg {}: {}, sort: {}", i, args[args.size()-1],
  //              sorts[sorts.size()-1]);
  // }
  // logger.Log(6, "ret_sort: {}", ret_sort);

  auto f = e.ctx().constant(name_stream.str().c_str(), ret_sort);
  // auto f = e.ctx().function(name_stream.str().c_str(), sorts, ret_sort);
  // logger.Log(6, "f: {}", f);
  // auto term = f(args);
  // logger.Log(6, "new term: {}", f);
  return f;
}


z3::sort Arrays2Fresh::AbstractSort(const z3::sort& s) const {
  if (s.is_bool()) return s;

  else if (s.is_array()) {
    if (abstract_arrays_) {
      // turn into its own uninterpreted sort
      return s.ctx().uninterpreted_sort(
          (uninterpreted_array_sort_name + SortName(s)).c_str());
    } else {
      // turn into term->term array, not supported by ANY LOGIC EVER
      auto domsort = s.array_domain();
      auto rasort = s.array_range();
      return s.ctx().array_sort(AbstractSort(domsort), AbstractSort(rasort));
    }
  } else {
    return s.ctx().uninterpreted_sort((uninterpreted_bv_sort_name +
                                       to_string(s.bv_size())).c_str());
  }
}

//^----------------------------------------------------------------------------^

  
void NukeArrays::collect_statistics(Statistics *st) const {
  st->Update("nuke arrays num_fresh_eqs", stats_.num_fresh_eqs);
  st->Update("nuke arrays num_fresh_selects", stats_.num_fresh_selects);
}

z3::expr NukeArrays::visitExpr(const z3::expr& e) {
  auto rw = make_identity_rewriter(NewArgsExprVector(e));
  return rw(e);
}


z3::expr NukeArrays::visitEQ(const z3::expr& e) {
  auto arg_0 = Arg(e, 0), arg_1 = Arg(e, 1);
  if (arg_0.get_sort().is_array() && arg_1.get_sort().is_array()) {
    ++stats_.num_fresh_eqs;
    auto name = fmt::format("arrayseq2bool-{}", unique_counter_++);
    auto b = e.ctx().bool_const(name.c_str());
    return b;
  }
  return visitExpr(e);
}


z3::expr NukeArrays::visitSELECT(const z3::expr& e) {
  ++stats_.num_fresh_selects;
  auto name = fmt::format("select2eq-{}", unique_counter_++);
  auto bv = e.ctx().constant(name.c_str(), e.get_sort());
  return bv;
}


//^----------------------------------------------------------------------------^

unique_ptr<EufBvSolver> EufBvSolver::clone() const {
  return make_unique<EufBvSolver>(*this);
}


//! Abstracts orig 
z3::expr EufBvSolver::Abstract(const z3::expr& orig) {
  auto [it, inserted] = abs2orig_.insert({(*abstract_)(orig), orig});
  if (!inserted) {
    // key alread exists
  }
  return it->first;
}

void EufBvSolver::Add(const z3::expr& e)  {
  // abstracts e's array ops and terms into UFs and then solve that
  auto e_abs = Abstract(e);
  if (!z3::eq(e_abs, e)) {
    // abstraction of e is not spurious
    found_non_spurious_abstraction_ = true;
  }
  solver().Add(e_abs);
}


CheckResult EufBvSolver::Check(const size_t n, const z3::expr* assumptions) {
  ++stats_.num_checks;
  // Abstracts assumptions before calling Check
  vector<z3::expr> assumptions_abs(n, z3::expr(ctx()));
  transform(assumptions, assumptions + n, assumptions_abs.begin(),
      [this](auto&& e) { return Abstract(e); });
  auto [assump, assump_abs] = mismatch(
      assumptions, assumptions + n, assumptions_abs.begin(),
      [](auto&& e1, auto&& e2) { return z3::eq(e1, e2); });
  (void)assump_abs;
  if (assump != assumptions + n) {
    logger.Log(6, "assumption {} is different", *assump_abs);
    // some abstraction non-spurious
    found_non_spurious_abstraction_ = true;
  }
  return solver().Check(assumptions_abs.size(), assumptions_abs.data());
}

void EufBvSolver::DumpBenchmark(
    std::ostream& os, size_t n, const z3::expr *assumptions) {
  if (n) {
    auto expr = expr_mk_and(ctx(), n, assumptions);
    auto solver = clone();
    solver->Add(expr);
    solver->DumpBenchmark(os, n, assumptions);
  } else {
    solver_->DumpBenchmark(os, 0, nullptr);
  }
}

z3::expr_vector EufBvSolver::unsat_core() {
  auto core = solver().unsat_core();
  z3::expr_vector core_orig(ctx());
  boost::transform(core, ExprVectorInserter(core_orig),
                   [&](auto&& e) { return abs2orig_.at(e); });
  return core_orig;
}

void EufBvSolver::collect_statistics(Statistics *st) const {
  // Don't want these names for right now...
  // Solver::collect_statistics(st);
  st->Update("eufbv_num_checks", stats_.num_checks);
}

} // end namespace euforia
