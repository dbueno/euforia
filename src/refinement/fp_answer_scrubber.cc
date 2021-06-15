// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "refinement/fp_answer_scrubber.h"

#include "supp/identity_rewriter.h"

namespace euforia {

z3::expr FpAnswerScrubber::operator()(const z3::expr& e) {
  return Rewrite(e);
}

z3::expr FpAnswerScrubber::visitExpr(const z3::expr& e) {
  if (!e.is_app()) {
    return make_identity_rewriter(NewArgsExprVector(e))(e);
  }
  // I don't do make_identity_rewriter here because...it doesn't do an
  // identity. For instance, it changes Boolean equalities into other Boolean
  // expressions which I don't want to do.
  return e.decl()(NewArgsExprVector(e));
}

z3::expr FpAnswerScrubber::visitBIT2BOOL(const z3::expr& e) {
  assert(Z3_get_decl_num_parameters(Z3_context(e.ctx()),
                                    Z3_func_decl(e.decl())) == 1);
  auto bit_idx = Z3_get_decl_int_parameter(Z3_context(e.ctx()),
                                           Z3_func_decl(e.decl()), 0);
  // Equivalant but uses EXTRACT instead
  auto bit_is_not_zero = e.arg(0).extract(bit_idx, bit_idx) != 0;
  return Rewrite(bit_is_not_zero);
}

} // end namespace euforia
