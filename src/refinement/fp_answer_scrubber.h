// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_FP_ANSWER_SCRUBBER_H_
#define EUFORIA_FP_ANSWER_SCRUBBER_H_

#include "supp/expr_rewriter.h"
#include "supp/expr_visitor.h"

namespace euforia {

class FpAnswerScrubber : public ExprRewriter<FpAnswerScrubber>,
    public ExprVisitor<FpAnswerScrubber, z3::expr> {
 public:

  //! Scrubs an fp.get_answer() of internal symbols
  z3::expr operator()(const z3::expr&);

  z3::expr visitExpr(const z3::expr&);

  // Internal expressions that crop up in an interpolant from the spacer
  z3::expr visitBIT2BOOL(const z3::expr&);
};

} // end namespace euforia

#endif
