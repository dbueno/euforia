// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef symex_hpp
#define symex_hpp

#include <cstdint>
#include <memory>
#include <propagate_const.h>

#include "supp/boolector_solver.h"
#include "xsys/transition_system.h"



namespace euforia {
class ExprSubstitution;

namespace vmt {
class AbstractVmtTransitionSystem;
}

namespace symex {
using namespace boolector;

class Executor;

using StateConstraint = Z3BtorExprPair;

//! A State represents a set of concrete program states as symbolic constraints
class State {
 public:
  State(Executor&, const ExprSet& concrete_init_constraints);
  State(const State&) = delete;
  // creates a state from given state
  State(const std::shared_ptr<State> other);
  State& operator=(const State&) = delete;
  ~State();

  z3::context& ctx() const;

  // this is a model of <some previous state> stepping to the preimage of this
  // state. i.e., the next-state variables in the model correspond to the
  // current state variables in this state.
  void set_pre_step_model(const std::shared_ptr<Model>& model) {
    pre_step_model_ = model;
  }

  std::shared_ptr<Model> pre_step_model() const {
    return pre_step_model_;
  }

  //*-------------------------------------------------------------------------------*
  //initialization

  /// Seed this state with a step from the state from which it was constructed
  void Simulate(const ExprSet& Ik, const ExprSet& Tk, const ExprSet& Ak_next);

  //*-------------------------------------------------------------------------------*
  //state and transition queries

  /// (Assume) the query for one step from this state using the given one-step constraints
  bool CheckOneStepQuery(const ExprSet& Ij, const ExprSet& Tj,
                         const ExprSet& Aj_next,
                         BtorCompleteAssignment *pre_state,
                         BtorCompleteAssignment *inputs,
                         BtorCompleteAssignment *next_state);


  //*-------------------------------------------------------------------------------*
  //
  const ExprSubstitution& passify_substitution() const;

  Executor& executor() const;

  ExprSet constraints() const;
  
  void Print(std::ostream& os) const;

 private:
  friend class Executor;
  bool simplify_next_states_ = false;
  // BtorCompleteAssignment one_step_pre_;
  // BtorCompleteAssignment one_step_inputs_;
  std::shared_ptr<Model> pre_step_model_;
  
  class Impl;
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;
};

std::ostream& operator<<(std::ostream& os, const State& s);


/*----------------------------------------------------------------------------*/

class Executor {
  friend class State; // gives state access to impl

  // BoolectorSolver& concrete_solver_;
  Solver& concrete_solver_;
  
 public:
  
  // all that have been created during this execution
  ExprSet inputConsts;

  // create initiale state from given constraints
  std::shared_ptr<State> InitState(const ExprSet& init_constraints);

  //! Returns true for SAT
  bool CheckState(const State&);

  //! Return value can be casted to BoolectorModel
  std::shared_ptr<Model> get_model();
  
  // extract next-state variable assignment from SAT result
  void RecordVarAssignment(
      int log_level,
      BtorCompleteAssignment *snext, BtorCompleteAssignment *scurr = nullptr,
      BtorCompleteAssignment *inputs = nullptr);
  
  Executor(const vmt::AbstractVmtTransitionSystem&, Solver&);
  ~Executor();

  inline const vmt::AbstractVmtTransitionSystem& ats() const { return axsys_; }
  
 private:
  const vmt::AbstractVmtTransitionSystem& axsys_;
  struct Impl;
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;
  
};
  
}
}

void mylog(const boolector::symex::State& s);


#endif /* symex_hpp */
