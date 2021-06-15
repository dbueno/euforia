// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef abstract_exprs_hpp
#define abstract_exprs_hpp

#include "supp/expr_rewriter.h"
#include "supp/expr_visitor.h"

namespace euforia {

// This code normalizes arithmetic relations to use only greater-than. Also, it
// reassociates associative operators to use binary versions. This helps the
// abstraction stay tight.
// XXX should be called NormalizeExpr
class NormalizeAbstractExpr : public ExprRewriter<NormalizeAbstractExpr>,
    public ExprVisitor<NormalizeAbstractExpr, z3::expr> {
 public:
  NormalizeAbstractExpr() {}
  
  //! Normalizes e
  z3::expr operator()(const z3::expr& e) {
    return Rewrite(e);
  }

  z3::expr visitExpr(const z3::expr&);
  
  z3::expr visitNOT(const z3::expr& e);
  z3::expr visitSGEQ(const z3::expr& e);
  z3::expr visitSLT(const z3::expr& e);
  z3::expr visitSLEQ(const z3::expr& e);
  z3::expr visitUGEQ(const z3::expr& e);
  z3::expr visitULT(const z3::expr& e);
  z3::expr visitULEQ(const z3::expr& e);
  z3::expr visitLE(const z3::expr&);
  z3::expr visitLT(const z3::expr&);
  z3::expr visitGE(const z3::expr&);
  z3::expr visitIFF(const z3::expr& e);
  
  z3::expr visitBAND(const z3::expr& e);
  z3::expr visitBOR(const z3::expr& e);
  z3::expr visitBXOR(const z3::expr& e);
  z3::expr visitBADD(const z3::expr&);
  z3::expr visitBMUL(const z3::expr&);
  z3::expr visitCONCAT(const z3::expr& e);

  z3::expr visitADD(const z3::expr&);
  z3::expr visitMUL(const z3::expr&);

 private:
  using ExprRewriter::Rewrite;
};
}

#endif /* abstract_exprs_hpp */
