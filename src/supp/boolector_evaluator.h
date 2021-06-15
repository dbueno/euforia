// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_BTOR_CONCRETIZING_EVALUATOR_H_
#define EUFORIA_BTOR_CONCRETIZING_EVALUATOR_H_

#include "supp/expr_rewriter.h"
#include "supp/expr_visitor.h"
#include "supp/solver.h"

namespace euforia {

//! Given a solver that is in a sat state, allows one to evaluate a concrete z3
//expression by looking up its values in the Boolector model
class BoolectorEvaluator : public ExprRewriter<BoolectorEvaluator, z3::expr>,
    public ExprVisitor<BoolectorEvaluator, z3::expr> {
 public:
  BoolectorEvaluator(Solver& s) : solver_(s) {}

  z3::expr Eval(const z3::expr&);

  // override of ExprRewriter::visitExpr
  z3::expr visitExpr(const z3::expr& e);

 private:
  Solver& solver_;
  using ExprRewriter::Rewrite;
};

}

#endif
