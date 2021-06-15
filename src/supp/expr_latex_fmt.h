// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef expr_latex_fmt_hpp
#define expr_latex_fmt_hpp

#include "supp/expr_visitor.h"

namespace euforia {

  class expr_LaTeX_visitor : public ExprVisitor<expr_LaTeX_visitor, std::ostream&> {
    
    std::ostream& os;
    
  public:
    expr_LaTeX_visitor();
    expr_LaTeX_visitor(std::ostream& os);
    
    void print(const z3::expr& e);
    
    std::ostream& visitExpr(const z3::expr& e);
    
#define DECL_HANDLER(ty)  std::ostream& visit##ty(const z3::expr& e)

    DECL_HANDLER(TRUE);
    DECL_HANDLER(FALSE);
    DECL_HANDLER(ANUM);
    DECL_HANDLER(BNUM);
    DECL_HANDLER(UNINTERPRETED);
    DECL_HANDLER(CONST_ARRAY);
    
    DECL_HANDLER(IMPLIES);
    DECL_HANDLER(BADD);
    DECL_HANDLER(BOR);
    DECL_HANDLER(BAND);
    DECL_HANDLER(BNOT);
    DECL_HANDLER(BXOR);
    DECL_HANDLER(AND);
    DECL_HANDLER(OR);
    DECL_HANDLER(NOT);
    DECL_HANDLER(BSREM0);
    DECL_HANDLER(BUREM0);
    DECL_HANDLER(CONCAT);
    DECL_HANDLER(EXTRACT);
    DECL_HANDLER(SIGN_EXT);

#undef DECL_HANDLER
  };
    
}


#endif /* expr_latex_fmt_hpp */
