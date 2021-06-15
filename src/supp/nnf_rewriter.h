// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_NNF_REWRITER_H_
#define EUFORIA_SUPP_NNF_REWRITER_H_

#include "supp/expr_rewriter.h"
#include "supp/expr_visitor.h"

namespace euforia {
//! Rewrites formula into negation normal form without introducing new
//! variables.
class NnfRewriter : public ExprRewriter<NnfRewriter>,
    public ExprVisitor<NnfRewriter, z3::expr> {
 public:
  NnfRewriter();

  z3::expr operator()(const z3::expr& e);

  z3::expr visitExpr(const z3::expr& e);
  z3::expr visitNOT(const z3::expr& e);
};
} // end namespace euforia

#endif
