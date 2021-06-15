// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_EXPR_FLATTENER_H_
#define EUFORIA_SUPP_EXPR_FLATTENER_H_

#include <deque>

#include "supp/expr_rewriter.h"
#include "supp/expr_supp.h"
#include "supp/expr_visitor.h"

namespace euforia {
//! Makes n-ary or's and and's
class ExprFlattener : public ExprRewriter<ExprFlattener>,
    public ExprVisitor<ExprFlattener, z3::expr> {
 public:
  ExprFlattener() {}

  z3::expr operator()(const z3::expr& e);
      
  // overrides
  z3::expr visitExpr(const z3::expr& e);
  z3::expr visitAND(const z3::expr& e);
  z3::expr visitOR(const z3::expr& e);

 private:
  ExprSet visited_;
  // Maps and/or node to its maximal list of children
  ExprMap<z3::expr_vector> flat_args_;
  std::deque<z3::expr> q_;
};

} // end namespace euforia

#endif
