// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef transition_system_coi_hpp
#define transition_system_coi_hpp

#include <memory>
#include <propagate_const.h>

#include "checker_types.h"
#include "supp/expr_supp.h"


namespace euforia {
class TransitionSystem;
class AbstractModel;

//*----------------------------------------------------------------------------*

class InfluenceTraversal {
 public:
  // filled in during traversal
  ExprSet vars_used;      // current-state vars found
  ExprSet vars_defd;      // next-state vars found
  ExprSet inputs_used;    // inputs found
  ExprSet constants_used; // constants found

  InfluenceTraversal(const TransitionSystem& ts, Z3EvalFunc eval, ExprSet *as);
  ~InfluenceTraversal();

  //! Finds the terms that may influence the targets
  //! 
  //! This method caches the predicate results so if it is called repeatedly on
  //! different targets, it dosen't do a lot of redundant computation.
  void operator()(const ExprSet& targets);

  void AddUsedVar(const z3::expr& e) { vars_used.insert(e); }
  void AddDefdVar(const z3::expr& e) { vars_defd.insert(e); }
  void AddUsedInput(const z3::expr& e) { inputs_used.insert(e); }
  void AddUsedConstant(const z3::expr& e) { constants_used.insert(e); }

 private:
  const TransitionSystem& ts_;
  Z3EvalFunc eval_;
  ExprSet *assumps_; // output during traversal
  struct Impl;
  std::unique_ptr<Impl> pimpl_;
};

}


#endif
