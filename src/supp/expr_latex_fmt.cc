// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "expr_latex_fmt.h"
#include "checker_types.h"

#include <ostream>

using namespace std;

namespace euforia {
  
  /// puts an escape before dollar signs
  static ostream& exprLaTeXEscape(ostream& os, const std::string& s) {
    // we assume this will be called in \text{} env
    for (auto ch : s) {
      switch(ch) {
        case '$':
          os << "\\$"; break;
        case '%':
          os << "\\%"; break;
        case '#':
          os << "\\#"; break;
        case '+':
          os << "$^+$"; break;
        case '^':
          os << "\\^"; break;
        case '_':
          os << "\\_"; break;
        default:
          os << ch;
          break;
      }
    }
    return os;
  }
  
  template <typename S>
  static ostream& exprLaTeXEscapeThing(ostream& os, const S& s) {
    stringstream ss;
    ss << s;
    return exprLaTeXEscape(os, ss.str());
  }

  
  /*-----------------------------------------------------------------------------------*/
  
  expr_LaTeX_visitor::expr_LaTeX_visitor() : os(std::cout) {}
  expr_LaTeX_visitor::expr_LaTeX_visitor(std::ostream& os) : os(os) {}
  
  void expr_LaTeX_visitor::print(const z3::expr& e) {
    visit(e);
  }
  
  std::ostream& expr_LaTeX_visitor::visitFALSE(const z3::expr&) { os << "0"; return os; }
  std::ostream& expr_LaTeX_visitor::visitTRUE(const z3::expr&) { os << "1"; return os; }
  std::ostream& expr_LaTeX_visitor::visitANUM(const z3::expr& e) { os << e; return os; }
  std::ostream& expr_LaTeX_visitor::visitBNUM(const z3::expr& e) {
    auto str = Z3_get_numeral_decimal_string(e.ctx(), e, 128);
    os << str << "^{[" << e.get_sort().bv_size() << "]}";
    return os;
  }
  std::ostream& expr_LaTeX_visitor::visitCONST_ARRAY(const z3::expr& e) {
    os << "\\text{array}(";
    os << "[\\text{";
    exprLaTeXEscapeThing(os, e.get_sort().array_domain()) << "} \\rightarrow \\text{";
    exprLaTeXEscapeThing(os, e.get_sort().array_range()) << "}], ";
    visit(e.arg(0));
    os << ")";
    return os;
  }
  
  std::ostream& expr_LaTeX_visitor::visitExpr(const z3::expr& e) {
    auto kind = e.decl().decl_kind();
    
    switch(e.num_args()) {
      case 0:
        os << "\\text{";
        exprLaTeXEscapeThing(os, e) << "}";
        break;
        
      case 2:
        
        if (kind == Z3_OP_SELECT) {
          visit(e.arg(0)) << "["; // array
          visit(e.arg(1)) << "]"; // addr
        } else {
          os << "(";
          visit(e.arg(0));
          os << "\\mathbin{";
          switch (kind) {
            case Z3_OP_EQ:
              os << "="; break;
            case Z3_OP_IFF:
              os << "=_{\\text{iff}}"; break;
            case Z3_OP_SLT:
              os << "<_s "; break;
            case Z3_OP_ULT:
              os << "<_u "; break;
            case Z3_OP_LT:
              os << "<"; break;
            case Z3_OP_SLEQ:
              os << "\\le_s "; break;
            case Z3_OP_ULEQ:
              os << "\\le_u "; break;
            case Z3_OP_LE:
              os << "\\le "; break;
            case Z3_OP_SGT:
              os << ">_s "; break;
            case Z3_OP_GT:
              os << ">"; break;
            case Z3_OP_UGT:
              os << ">_u "; break;
            case Z3_OP_DISTINCT:
              os << "\\ne "; break;
            case Z3_OP_BMUL:
              os << "\\cdot "; break;
            case Z3_OP_BSHL:
              os << "\\ll "; break;
            case Z3_OP_BASHR:
              os << "\\gg_a "; break;
            case Z3_OP_BLSHR:
              os << "\\gg_l "; break;
            case Z3_OP_BOR:
              os << " $|$ "; break;
            case Z3_OP_BSREM_I:
              os << "\\%_{si} "; break;
            case Z3_OP_BUREM_I:
              os << "\\%_{ui} "; break;
            case Z3_OP_BSDIV_I:
              os << " /_{si} "; break;
            case Z3_OP_BUDIV_I:
              os << " /_{ui} "; break;
              
            default:
              EUFORIA_FATAL(e);
          }
          os << "}";
          visit(e.arg(1));
          os << ")";
        }
        
        break;
        
      case 3:
        switch (kind) {
          case Z3_OP_ITE:
            os << "\\text{ITE}(";
            visit(e.arg(0)) << ", ";
            visit(e.arg(1)) << ", ";
            visit(e.arg(2)) << ")";
            break;
            
          case Z3_OP_STORE:
            visit(e.arg(0)); // array
            os << "[";
            visit(e.arg(1)); // addr
            os << " \\gets  ";
            visit(e.arg(2)); // value
            os << "]";
            break;
            
          default:
            EUFORIA_FATAL(e);
        }
        break;
        
      default:
        EUFORIA_FATAL(e);
    }
    return os;
  }

  std::ostream& expr_LaTeX_visitor::visitUNINTERPRETED(const z3::expr &e) {
    os << "\\text{";
    exprLaTeXEscape(os, e.decl().name().str()) << "}";
    if (e.num_args() > 0) {
      os << "(";
      for (unsigned i = 0; i < e.num_args(); i++) {
        if (i > 0) os << ", ";
        visit(e.arg(i));
      }
      os << ")";
    }
    return os;
  }
  
  std::ostream& expr_LaTeX_visitor::visitIMPLIES(const z3::expr &e) {
    visit(e.arg(0));
    os << "\\Rightarrow ";
    visit(e.arg(1));
    return os;
  }
  
  std::ostream& expr_LaTeX_visitor::visitBADD(const z3::expr& e) {
    os << "(";
    for (unsigned i = 0; i < e.num_args(); i++) {
      if (i > 0)
        os << "+ ";
      visit(e.arg(i));
    }
    os << ")";
    return os;
  }

  std::ostream& expr_LaTeX_visitor::visitBOR(const z3::expr& e) {
    os << "(";
    for (unsigned i = 0; i < e.num_args(); i++) {
      if (i > 0)
        os << "~|~";
      visit(e.arg(i));
    }
    os << ")";
    return os;
  }

  std::ostream& expr_LaTeX_visitor::visitBAND(const z3::expr& e) {
    os << "(";
    for (unsigned i = 0; i < e.num_args(); i++) {
      if (i > 0)
        os << "~\\text{&}~";
      visit(e.arg(i));
    }
    os << ")";
    return os;
  }

  std::ostream& expr_LaTeX_visitor::visitBXOR(const z3::expr& e) {
    os << "(";
    for (unsigned i = 0; i < e.num_args(); i++) {
      if (i > 0)
        os << "\\oplus ";
      visit(e.arg(i));
    }
    os << ")";
    return os;
  }

  std::ostream& expr_LaTeX_visitor::visitBNOT(const z3::expr& e) {
    assert(e.num_args()==1);
    os << "\\sim";
    visit(e.arg(0));
    return os;
  }

  std::ostream& expr_LaTeX_visitor::visitNOT(const z3::expr& e) {
    assert(e.num_args()==1);
    os << "\\neg";
    visit(e.arg(0));
    return os;
  }


  std::ostream& expr_LaTeX_visitor::visitAND(const z3::expr& e) {
    os << "(";
    for (unsigned i = 0; i < e.num_args(); i++) {
      if (i > 0)       os << "\\wedge ";
      visit(e.arg(i));
    }
    os << ")";
    return os;
  }
  
  std::ostream& expr_LaTeX_visitor::visitOR(const z3::expr& e) {
    os << "(";
    for (unsigned i = 0; i < e.num_args(); i++) {
      if (i > 0)       os << "\\vee ";
      visit(e.arg(i));
    }
    os << ")";
    return os;
  }
  
  std::ostream& expr_LaTeX_visitor::visitCONCAT(const z3::expr& e) {
    os << "\\text{concat}(";
    for (unsigned i = 0; i < e.num_args(); i++) {
      if (i > 0) os << ", ";
      visit(e.arg(i));
    }
    os << ")";
    return os;
  }
  
  std::ostream& expr_LaTeX_visitor::visitEXTRACT(const z3::expr& e) {
    assert(e.num_args()==1);
    assert(Z3_get_decl_num_parameters(e.ctx(), e.decl()) == 2);
    auto hi = Z3_get_decl_int_parameter(e.ctx(), e.decl(), 0);
    auto lo = Z3_get_decl_int_parameter(e.ctx(), e.decl(), 1);
    os << "\\text{extract}(" << hi << ", " << lo << ", ";
    visit(e.arg(0));
    os << ")";
    return os;
  }

  std::ostream& expr_LaTeX_visitor::visitSIGN_EXT(const z3::expr& e) {
    assert(e.num_args()==1);
    assert(Z3_get_decl_num_parameters(e.ctx(), e.decl()) == 1);
    auto addedBits = Z3_get_decl_int_parameter(e.ctx(), e.decl(), 0);
    os << "\\text{sext}(";
    os << addedBits << ", ";
    visit(e.arg(0));
    os << ")";
    return os;
  }
  
  std::ostream& expr_LaTeX_visitor::visitBSREM0(const z3::expr& e) {
    assert(e.num_args()==1);
    os << "\\text{bsrem}_0(";
    visit(e.arg(0));
    os << ")";
    return os;
  }

  std::ostream& expr_LaTeX_visitor::visitBUREM0(const z3::expr& e) {
    assert(e.num_args()==1);
    os << "\\text{burem}_0(";
    visit(e.arg(0));
    os << ")";
    return os;
  }

}
