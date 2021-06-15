// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef expr_visitor_hpp
#define expr_visitor_hpp

#include <z3++.h>

#include "checker_types.h"

namespace euforia {
template <typename SubClass, typename RetTy=void, typename ExprTy=z3::expr>
class ExprVisitor {
 public:
  // override this in a subclass if you are visiting some type that you can get
  // a node from
  z3::expr get_visit_node(const ExprTy& e) {
    return e;
  }

  // Call this to start things off
  RetTy visit(const ExprTy& e) {
    auto node = static_cast<SubClass*>(this)->get_visit_node(e);
    switch (node.kind()) {
      case Z3_VAR_AST:
        return static_cast<SubClass*>(this)->visitVAR(e);
      case Z3_QUANTIFIER_AST:
        return static_cast<SubClass*>(this)->visitQUANTIFIER(e);
      case Z3_APP_AST:
      case Z3_NUMERAL_AST:
        switch (node.decl().decl_kind()) {
#define HANDLE_KIND(OP) case Z3_OP_##OP: return static_cast<SubClass*>(this)->visit##OP(e);
          HANDLE_KIND(UNINTERPRETED);
          // logical
          HANDLE_KIND(TRUE);
          HANDLE_KIND(FALSE);
          HANDLE_KIND(EQ);
          HANDLE_KIND(IFF);
          HANDLE_KIND(DISTINCT);
          HANDLE_KIND(NOT);
          HANDLE_KIND(AND);
          HANDLE_KIND(OR);
          HANDLE_KIND(XOR);
          HANDLE_KIND(ITE);
          HANDLE_KIND(IMPLIES);

          // int
          HANDLE_KIND(ANUM);
          HANDLE_KIND(ADD);
          HANDLE_KIND(SUB);
          HANDLE_KIND(UMINUS);
          HANDLE_KIND(MUL);
          HANDLE_KIND(DIV);
          HANDLE_KIND(IDIV);
          HANDLE_KIND(REM);
          HANDLE_KIND(MOD);
          HANDLE_KIND(LE);
          HANDLE_KIND(LT);
          HANDLE_KIND(GE);
          HANDLE_KIND(GT);

          HANDLE_KIND(TO_REAL);
          HANDLE_KIND(TO_INT);
          HANDLE_KIND(IS_INT);
          HANDLE_KIND(POWER);

          // array
          HANDLE_KIND(STORE);
          HANDLE_KIND(SELECT);
          HANDLE_KIND(CONST_ARRAY);
          HANDLE_KIND(AS_ARRAY);
          HANDLE_KIND(ARRAY_DEFAULT);
          HANDLE_KIND(ARRAY_MAP);
          HANDLE_KIND(ARRAY_EXT);

          HANDLE_KIND(SET_UNION);
          HANDLE_KIND(SET_INTERSECT);
          HANDLE_KIND(SET_DIFFERENCE);
          HANDLE_KIND(SET_COMPLEMENT);
          HANDLE_KIND(SET_SUBSET);

          // bitvec
          HANDLE_KIND(BNUM);
          HANDLE_KIND(BIT1);
          HANDLE_KIND(BIT0);
          HANDLE_KIND(BIT2BOOL);
          HANDLE_KIND(BADD);
          HANDLE_KIND(BMUL);
          HANDLE_KIND(BSUB);
          HANDLE_KIND(BSDIV);
          HANDLE_KIND(BSDIV0);
          HANDLE_KIND(BSDIV_I);
          HANDLE_KIND(BUDIV);
          HANDLE_KIND(BUDIV0);
          HANDLE_KIND(BUDIV_I);
          HANDLE_KIND(BSREM);
          HANDLE_KIND(BSREM0);
          HANDLE_KIND(BSREM_I);
          HANDLE_KIND(BUREM);
          HANDLE_KIND(BUREM0);
          HANDLE_KIND(BUREM_I);
          HANDLE_KIND(BSMOD);
          HANDLE_KIND(BSMOD_I);
          HANDLE_KIND(BSHL);
          HANDLE_KIND(BASHR);
          HANDLE_KIND(BLSHR);
          HANDLE_KIND(CONCAT);
          HANDLE_KIND(EXTRACT);
          HANDLE_KIND(SIGN_EXT);
          HANDLE_KIND(ZERO_EXT);
          HANDLE_KIND(SLT);
          HANDLE_KIND(SLEQ);
          HANDLE_KIND(SGT);
          HANDLE_KIND(SGEQ);
          HANDLE_KIND(ULT);
          HANDLE_KIND(ULEQ);
          HANDLE_KIND(UGT);
          HANDLE_KIND(UGEQ);
          HANDLE_KIND(BNEG);
          HANDLE_KIND(BAND);
          HANDLE_KIND(BOR);
          HANDLE_KIND(BXOR);
          HANDLE_KIND(BNOR);
          HANDLE_KIND(BNOT);
          HANDLE_KIND(REPEAT);
          HANDLE_KIND(BREDAND);
          HANDLE_KIND(BCOMP);
          HANDLE_KIND(ROTATE_LEFT);
          HANDLE_KIND(ROTATE_RIGHT);
          HANDLE_KIND(EXT_ROTATE_LEFT);
          HANDLE_KIND(EXT_ROTATE_RIGHT);
          HANDLE_KIND(INT2BV);
          HANDLE_KIND(BV2INT);
          HANDLE_KIND(CARRY);
          HANDLE_KIND(XOR3);
          HANDLE_KIND(BSMUL_NO_OVFL);
          HANDLE_KIND(BUMUL_NO_OVFL);
          HANDLE_KIND(BSMUL_NO_UDFL);

          HANDLE_KIND(AGNUM);

          default:
          EUFORIA_FATAL(fmt::format("unhandled Z3 operator: {}", node));
#undef HANDLE_KIND

        }

      default:
        EUFORIA_FATAL(fmt::format("unhandled AST: {}", node));
    }
  }
    
  // default case. you must override this if return type is not void
  void visitExpr(const z3::expr&) {} // ignore
    
    
  RetTy visitVAR(const ExprTy& e) {
    return static_cast<SubClass*>(this)->visitExpr(e);
  }

  RetTy visitQUANTIFIER(const ExprTy& e) {
    return static_cast<SubClass*>(this)->visitExpr(e);
  }

#define DELEGATE(KIND) RetTy visit##KIND(const ExprTy& e) { \
  return static_cast<SubClass*>(this)->visitExpr(e); }
  DELEGATE(UNINTERPRETED);
  DELEGATE(TRUE);
  DELEGATE(FALSE);
  DELEGATE(EQ);
  DELEGATE(IFF);
  DELEGATE(DISTINCT);
  DELEGATE(NOT);
  DELEGATE(AND);
  DELEGATE(OR);
  DELEGATE(XOR);
  DELEGATE(ITE);
  DELEGATE(IMPLIES);

  DELEGATE(ANUM);
  DELEGATE(ADD);
  DELEGATE(SUB);
  DELEGATE(UMINUS);
  DELEGATE(MUL);
  DELEGATE(DIV);
  DELEGATE(IDIV);
  DELEGATE(REM);
  DELEGATE(MOD);
  DELEGATE(LE);
  DELEGATE(LT);
  DELEGATE(GE);
  DELEGATE(GT);

  DELEGATE(TO_REAL);
  DELEGATE(TO_INT);
  DELEGATE(IS_INT);
  DELEGATE(POWER);

  DELEGATE(BNUM);
  DELEGATE(BIT1);
  DELEGATE(BIT0);
  DELEGATE(BIT2BOOL);
  DELEGATE(BADD);
  DELEGATE(BSUB);
  DELEGATE(BMUL);
  DELEGATE(BSDIV);
  DELEGATE(BSDIV0);
  DELEGATE(BSDIV_I);
  DELEGATE(BUDIV);
  DELEGATE(BUDIV0);
  DELEGATE(BUDIV_I);
  DELEGATE(BSREM);
  DELEGATE(BSREM0);
  DELEGATE(BSREM_I);
  DELEGATE(BUREM);
  DELEGATE(BUREM0);
  DELEGATE(BUREM_I);
  DELEGATE(BSMOD);
  DELEGATE(BSMOD_I);
  DELEGATE(BSHL);
  DELEGATE(BASHR);
  DELEGATE(BLSHR);
  DELEGATE(CONCAT);
  DELEGATE(EXTRACT);
  DELEGATE(SIGN_EXT);
  DELEGATE(ZERO_EXT);
  DELEGATE(SLT);
  DELEGATE(SLEQ);
  DELEGATE(SGT);
  DELEGATE(SGEQ);
  DELEGATE(ULT);
  DELEGATE(ULEQ);
  DELEGATE(UGT);
  DELEGATE(UGEQ);
  DELEGATE(BNEG);
  DELEGATE(BAND);
  DELEGATE(BOR);
  DELEGATE(BXOR);
  DELEGATE(BNOR);
  DELEGATE(BNOT);
  DELEGATE(REPEAT);
  DELEGATE(BREDAND);
  DELEGATE(BCOMP);
  DELEGATE(ROTATE_LEFT);
  DELEGATE(ROTATE_RIGHT);
  DELEGATE(EXT_ROTATE_LEFT);
  DELEGATE(EXT_ROTATE_RIGHT);
  DELEGATE(INT2BV);
  DELEGATE(BV2INT);
  DELEGATE(CARRY);
  DELEGATE(XOR3);
  DELEGATE(BSMUL_NO_OVFL);
  DELEGATE(BUMUL_NO_OVFL);
  DELEGATE(BSMUL_NO_UDFL);

  DELEGATE(STORE);
  DELEGATE(SELECT);
  DELEGATE(CONST_ARRAY);
  DELEGATE(AS_ARRAY);
  DELEGATE(ARRAY_DEFAULT);
  DELEGATE(ARRAY_MAP);
  DELEGATE(ARRAY_EXT);

  DELEGATE(AGNUM);
      
  DELEGATE(SET_UNION);
  DELEGATE(SET_INTERSECT);
  DELEGATE(SET_DIFFERENCE);
  DELEGATE(SET_COMPLEMENT);
  DELEGATE(SET_SUBSET);

#undef DELEGATE
 
 protected:
  ExprVisitor() = default;
  ~ExprVisitor() = default;
 
};

}

#endif
