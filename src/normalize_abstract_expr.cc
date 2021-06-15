// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "normalize_abstract_expr.h"
#include "supp/expr_supp.h"
#include "supp/identity_rewriter.h"

using namespace std;

namespace euforia {

z3::expr NormalizeAbstractExpr::visitExpr(const z3::expr& e) {
  return make_identity_rewriter(NewArgsExprVector(e))(e);
}

//^----------------------------------------------------------------------------^
// This code normalizes arithmetic relations to use only greater-than. It also
// takes care to not introduce disjunctions: each relation is changed to
// exactly one occurrence of greater-than (possible swapping arguments). It
// preserves the signedness of the operators -- it should be an exactly
// equivalent formula.

#define DEFINE_NORM_CMP(name, exp) \
    z3::expr NormalizeAbstractExpr::visit##name(const z3::expr& e) { \
      assert(e.num_args() == 2); \
      auto a = Arg(e,0), b = Arg(e,1); \
      auto ret = (exp); \
      return ret; \
    }

#if 1
DEFINE_NORM_CMP(SGEQ, !(b > a));
DEFINE_NORM_CMP(SLT, (b > a));
DEFINE_NORM_CMP(UGEQ, !z3::ugt(b, a));
DEFINE_NORM_CMP(ULT, z3::ugt(b, a));

#else
// alternate defs
DEFINE_NORM_CMP(SGEQ, (a == b) || (a > b));
DEFINE_NORM_CMP(SLT, (a != b) && !(a > b));
DEFINE_NORM_CMP(UGEQ, (a == b) || z3::ugt(a, b));
DEFINE_NORM_CMP(ULT, (a != b) && !z3::ugt(a, b));
#endif
DEFINE_NORM_CMP(SLEQ, !(a > b));
DEFINE_NORM_CMP(ULEQ, !z3::ugt(a, b));
DEFINE_NORM_CMP(GE, !(b > a));
DEFINE_NORM_CMP(LT, (b > a));
DEFINE_NORM_CMP(LE, !(a > b));

DEFINE_NORM_CMP(IFF, (a && b) || (!a && !b));

// Applies expr_not just to remove things like (not (not (not ...)))
z3::expr NormalizeAbstractExpr::visitNOT(const z3::expr& e) {
  return expr_not(Arg(e,0));
}

//^----------------------------------------------------------------------------^
// Converts associative operations from n-ary applications to 2-ary
// applications.  This way the abstraction only has one ADD function for
// example, instead of multiple ADD functions that are obviously related.

#define REASSOCIATE_NARY(e, binop) { \
  z3::expr ret(e.ctx()); \
  const int num_args = static_cast<int>(e.num_args()); \
  assert(num_args > 1); \
  if (num_args > 2) { \
    int i = static_cast<int>(num_args); \
    do { \
      i--; \
      ret = bool(ret) ? binop(Arg(e,i), ret) : Arg(e,i); \
      assert(i == num_args-1 || ret.num_args() == 2); \
    } while (i > 0); \
  } else { \
    ret = visitExpr(e); \
  } \
  return ret; \
}

z3::expr NormalizeAbstractExpr::visitBAND(const z3::expr& e) {
  REASSOCIATE_NARY(e, operator&);
}

z3::expr NormalizeAbstractExpr::visitBOR(const z3::expr& e) {
  REASSOCIATE_NARY(e, operator|);
}

z3::expr NormalizeAbstractExpr::visitBXOR(const z3::expr& e) {
  REASSOCIATE_NARY(e, operator^);
}

z3::expr NormalizeAbstractExpr::visitCONCAT(const z3::expr& e) {
  REASSOCIATE_NARY(e, z3::concat);
}

z3::expr NormalizeAbstractExpr::visitBADD(const z3::expr& e) {
  REASSOCIATE_NARY(e, operator+);
}

z3::expr NormalizeAbstractExpr::visitBMUL(const z3::expr& e) {
  REASSOCIATE_NARY(e, operator*);
}

z3::expr NormalizeAbstractExpr::visitADD(const z3::expr& e) {
  REASSOCIATE_NARY(e, operator+);
}

z3::expr NormalizeAbstractExpr::visitMUL(const z3::expr& e) {
  REASSOCIATE_NARY(e, operator*);
}

}
