// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "cube.h"
#include "tslice.h"
#include "symex.h"
#include "supp/std_supp.h"
#include "supp/expr_supp.h"
#include "supp/expr_iterators.h"
#include "supp/expr_set_traversal.h"
#include "xsys/abstract_vmt_transition_system.h"
#include "xsys/var_info_traversal.h"
#include "supp/expr_substitution.h"

#include <boost/range/algorithm/for_each.hpp>
#include <boost/iterator/function_output_iterator.hpp>
#include <llvm/ADT/FoldingSet.h>

#include <type_traits>
#include <utility>

using namespace std;
using namespace llvm;
using namespace euforia::vmt;

namespace euforia::symex {

//*-------------------------------------------------------------------------------*

struct StateConstraintHash {
  size_t operator()(const StateConstraint& key) const {
    FoldingSetNodeID ret;
    ret.AddInteger(key.z3_node().hash());
    ret.AddInteger(key.btor_node().hash());
    return ret.ComputeHash();
  }
};

struct StateConstraintEqual {
  bool operator()(const StateConstraint& x, const StateConstraint& y) const {
    return x == y;
  }
};

using StateConstraintSet = unordered_set<StateConstraint, StateConstraintHash,
      StateConstraintEqual>;

//*-------------------------------------------------------------------------------*
//State::Impl

#ifndef SYMEX_STATE_WITH_VAR_MAP

#include "symex_state_impl_constraints.inc"

#else

#include "symex_state_impl_var_map.inc"

#endif

//*-------------------------------------------------------------------------------*
//State

const ExprSubstitution& State::passify_substitution() const {
  return pimpl_->passify_inputs_;
}

State::State(Executor& E, const ExprSet& state_constraints) 
    : pimpl_(std::make_unique<State::Impl>(E, E.ats().cts(),
                                           state_constraints)) {
}

State::State(const shared_ptr<State> other) 
    : pimpl_(std::make_unique<State::Impl>(*other->pimpl_)) {
}
  
State::~State() {}
  
z3::context& State::ctx() const {
  return pimpl_->cts_.ctx();
}

std::ostream& operator<<(std::ostream& os, const State& s) {
  s.Print(os);
  return os;
}


//void State::RecordVarAssignment(const boolector::BtorCompleteAssignment& ass) {
//}

bool State::CheckOneStepQuery(
    const ExprSet& Ij, const ExprSet& Tj, const ExprSet& Aj_next,
    BtorCompleteAssignment *pre_state, BtorCompleteAssignment *inputs,
    BtorCompleteAssignment *next_state) {
  abort();
  // XXX this function should take in a State, not all these stuped params. Those things should be stashed in the state after the executor does the query with the state
  (void)Ij;
  (void)Tj;
  (void)Aj_next;
  (void)pre_state;
  (void)inputs;
  (void)next_state;
  // static int query_num = 0;
  // BoolectorSolver& concrete_solver = pimpl_->symex_.concrete_solver_;
  // pimpl_->AssumeState();
  // for (auto& e : Ij) {
  //   concrete_solver.Assume(pimpl_->MapConcreteExpr(pimpl_->ats_.Concretize(e)),
  //                          true, string("input"));
  // }
  // for (auto& e : Tj) {
  //   concrete_solver.Assume(pimpl_->MapConcreteExpr(pimpl_->ats_.Concretize(e)),
  //                          true, string("transition"));
  // }
  // for (auto& e : Aj_next) {
  //   concrete_solver.Assume(pimpl_->MapConcreteExpr(pimpl_->ats_.Concretize(e)),
  //                          true, string("next cube"));
  // }
  // if (!LOG_DIR.empty()) {
  //   ofstream outfile(fmt::format("{}/RefFwd{}.smt2", LOG_DIR,
  //                                query_num++));
  //   concrete_solver.btor_solver()->DumpBenchmark(outfile);
  //   outfile.close();
  // }
  // auto ret = concrete_solver.Check();
  // if (ret == CheckResult::kSat && next_state) 
  //   executor().RecordVarAssignment(5, next_state, pre_state, inputs);
  // return ret == CheckResult::kSat;
}

void State::Simulate(const ExprSet& Ik, const ExprSet& Tk, const ExprSet& Ak_next) {
  pimpl_->Simulate(simplify_next_states_, Ik, Tk, Ak_next);
}


/*----------------------------------------------------------------------------*/

Executor& State::executor() const {
  return pimpl_->executor();
}

ExprSet State::constraints() const {
  return pimpl_->constraints();
}


void State::Print(std::ostream& os) const {
  fmt::print(os, "symex::State:\n");
  pimpl_->Print(os);
  if (pre_step_model_) {
    fmt::print(os, "    pre-step model:\n");
    fmt::print(os, "{}\n", *pre_step_model_);
  }
  // fmt::print(os, "    prestate assignment from one-step:\n");
  // for (auto& [name, ass] : one_step_pre_) {
  //   fmt::print(os, "      {}: ", name);
  //   ass->print(os);
  //   fmt::print(os, "\n");
  // }
  // fmt::print(os, "    input assignment from one-step:\n");
  // for (auto& [name, ass] : one_step_inputs_) {
  //   fmt::print(os, "      {}: ", name);
  //   ass->print(os);
  //   fmt::print(os, "\n");
  // }
}



/*-----------------------------------------------------------------------------------*/

struct Executor::Impl {
  Impl() {}
};

/*----------------------------------------------------------------------------*/


Executor::Executor(const AbstractVmtTransitionSystem& axsys,
                   Solver& concrete_solver)
    : axsys_(axsys), concrete_solver_(concrete_solver),
    pimpl_(std::make_unique<Executor::Impl>()) {
}
  
Executor::~Executor() {}

std::shared_ptr<State> Executor::InitState(const ExprSet& constraints) {
  auto st = make_shared<State>(*this, constraints);
  return st;
}

bool Executor::CheckState(const State& s) {
  vector<z3::expr> assumps;
  copy(s.constraints().begin(), s.constraints().end(), back_inserter(assumps));
  bool ret;
  
  logger.Log(5, "Executor::CheckState");
  auto result = concrete_solver_.Check(assumps);
  switch (result) {
    case CheckResult::kUnsat:
      ret = false;
      break;
      
    case CheckResult::kSat:
      ret = true;
      break;
      
    default:
      EUFORIA_FATAL("UNKNOWN");
  }
  
  return ret;
}

shared_ptr<Model> Executor::get_model() {
  const auto& cxsys = axsys_.cts();
  z3::expr_vector vars(cxsys.ctx());
  transform(cxsys.vbegin(), cxsys.vend(), ExprVectorInserter(vars),
            [](auto&& v) { return v.current(); });
  transform(cxsys.vbegin(), cxsys.vend(), ExprVectorInserter(vars),
            [](auto&& v) { return v.next(); });
  transform(cxsys.ibegin(), cxsys.iend(), ExprVectorInserter(vars),
            [](const z3::expr& i) { return i; });
  return concrete_solver_.get_model(vars);
  // stringstream sout;
  // sout << "  checkState SAT assignment:" << endl;
  // for (auto varit = cts.vbegin(), varend = cts.vend(); varit != varend; ++varit) {
  //   auto& var = *varit;
  //   auto btorVar = pimpl_->z3_to_btor_.Rewrite(var.current());
  //   auto ass = concrete_solver.btor_solver()->assignment(btorVar);
  //   ass_out->insert({var.name(), ass});
  //   sout << "  " << *ass << endl;
  // }
  // logger.Log(6, "{{{{{{{}}}}}}}", sout.str());
}


void Executor::RecordVarAssignment(
    int log_level,
    BtorCompleteAssignment *snext,
    BtorCompleteAssignment *scurr,
    BtorCompleteAssignment *inputs) {
  abort();
  (void)log_level;
  (void)snext;
  (void)scurr;
  (void)inputs;
//#ifdef LOGGER_ON
//  StateVarMap<std::pair<std::shared_ptr<BtorAssignment>, std::shared_ptr<BtorAssignment>>> changedVars;
//  StateVarMap<std::shared_ptr<BtorAssignment>> preservedVars;
//#endif
//  auto& btor_solver = *concrete_solver_.btor_solver();
//  for (auto varit = axsys_.cts().vbegin(), varend = axsys_.cts().vend();
//       varit != varend; ++varit) {
//    const StateVar& var = *varit;
//    auto var_btor = concrete_solver_.MapConcreteExpr(var.current()).btor_node();
//    //assert(var_btor.isVar() || var_btor.isArray());
//    auto var_btor_next = concrete_solver_.MapConcreteExpr(var.next()).btor_node();
//    //assert(var_btor_next.isVar() || var_btor_next.isArray());
//    auto var_btor_assignment = btor_solver.assignment(var_btor);
//    auto var_btor_assignment_next = btor_solver.assignment(var_btor_next);
//    logger.Log(log_level, "{} => {}", *var_btor_assignment, *var_btor_assignment_next);
//    if (scurr)
//      scurr->emplace(make_pair(var.name(), var_btor_assignment));
//    if (snext)
//      snext->emplace(make_pair(var.name(), var_btor_assignment_next));
//    // prints a * if the variable is modified in the step
//#ifdef LOGGER_ON
//    if (*var_btor_assignment != *var_btor_assignment_next) {
//      changedVars.emplace(make_pair(ref(var), make_pair(var_btor_assignment, var_btor_assignment_next)));
//    } else {
//      preservedVars.emplace(make_pair(ref(var), var_btor_assignment));
//    }
//#endif
//  }
  
//  if (inputs) {
//    for (auto it = axsys_.cts().ibegin(), ie = axsys_.cts().iend();
//         it != ie; ++it) {
//      const PrimaryInput& PI = *it;
//      auto btorPI = concrete_solver_.MapConcreteExpr(PI.z).btor_node();
//      auto assPI = btor_solver.assignment(btorPI);
//      inputs->insert({PI.name, assPI});
//    }
//  }
  
//#ifdef LOGGER_ON
//  if (logger.ShouldLog(log_level)) {
//    logger.Log(log_level, "{} changed vars:", changedVars.size());
//    for (auto& entry : changedVars) {
//      const auto& var_btor_assignment = entry.second.first, &var_btor_assignment_next = entry.second.second;
//      const StateVar& var = entry.first;
//      if (var.is_location()) { // location
//        auto bvAssNext = std::static_pointer_cast<BtorBvAssignment>(var_btor_assignment_next);
//        logger.Log(log_level, "{}", *var_btor_assignment_next);
//      } else {
//        logger.Log(log_level, "ass:     {}", *var_btor_assignment);
//        logger.Log(log_level, "var_btor_assignment_next: {}", *var_btor_assignment_next);
//      }
//    }
//  }
//#endif
//  //LOG(log, "{} preserved vars:", preservedVars.size());
//  //for (auto& entry : preservedVars) {
//  //  auto ass = entry.second;
//  //  outputVarAssignment(ass);
//  //}
}



}

void mylog(const euforia::symex::State& s) {
  s.Print(cerr);
}
