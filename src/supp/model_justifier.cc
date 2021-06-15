// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/model_justifier.h"

#include "supp/debug.h"
#include "supp/identity_rewriter.h"
#include "supp/equality_literal.h"

using namespace std;

namespace euforia {
  
template <>
bool ModelJustifier::AddPredicate(const z3::expr& e) {
#ifdef EXPENSIVECHECKS
  EUFORIA_ASSERT(IsLiteral(e), "not a literal: {}", e);
  EUFORIA_ASSERT(
      is_literal_true(Eval(e)),
      "e does not eval to true\n" "e: {}\n" "e eval: {}\n",
      e, Eval(e));
#endif
  if (predicates_)
    return predicates_->insert(e).second;
  else
    return true;
}

template <>
z3::expr ModelJustifier::Eval(const StackElt& elt) {
  if (bool(elt.node_eval)) {
    return elt.node_eval;
  } else {
    return Eval(elt.node);
  }
}

template <>
z3::expr ModelJustifier::visitExpr(const StackElt& elt) {
  auto& e = elt.node;
  auto decl = e.decl();
  auto kind = decl.decl_kind();
  switch (kind) {
    // things that can go in literals
    case Z3_OP_UNINTERPRETED:
    case Z3_OP_FALSE:
    case Z3_OP_TRUE:
    case Z3_OP_ANUM:
    case Z3_OP_MOD:
    case Z3_OP_ADD:
    case Z3_OP_BNUM:
    case Z3_OP_BADD:
    case Z3_OP_BMUL:
    case Z3_OP_SELECT:
    case Z3_OP_STORE:
    case Z3_OP_CONST_ARRAY:
    case Z3_OP_LT:
    case Z3_OP_SLT:
    case Z3_OP_LE:
    case Z3_OP_SLEQ:
    case Z3_OP_GT:
    case Z3_OP_SGT:
    case Z3_OP_ULT:
    case Z3_OP_ULEQ:
    case Z3_OP_UGT:
    case Z3_OP_UGEQ:
    case Z3_OP_BAND:
    case Z3_OP_BOR:
    case Z3_OP_BNOT:
    case Z3_OP_BXOR:
    case Z3_OP_BNAND:
    case Z3_OP_BNOR:
    case Z3_OP_BXNOR:
    case Z3_OP_BSDIV:
    case Z3_OP_BUDIV:
    case Z3_OP_BSREM:
    case Z3_OP_BUREM:
    case Z3_OP_BSMOD:
    case Z3_OP_BSDIV_I:
    case Z3_OP_BUDIV_I:
    case Z3_OP_BSREM_I:
    case Z3_OP_BUREM_I:
    case Z3_OP_BSMOD_I:
    case Z3_OP_CONCAT:
    case Z3_OP_SIGN_EXT:
    case Z3_OP_ZERO_EXT:
    case Z3_OP_EXTRACT:
    case Z3_OP_BSHL:
    case Z3_OP_BLSHR:
    case Z3_OP_BASHR:
      return make_identity_rewriter(NewArgsExprVector(e))(e);

    // These are handled dually so I made them one piece of code.
    case Z3_OP_AND:
    case Z3_OP_OR: {
      auto& e_eval = elt.node_eval;
      z3::expr ret(e.ctx());
      // Tests whether we only need to look at a "single" arg for an AND or OR.
      const auto single_case = kind == Z3_OP_AND ?
          is_literal_false : is_literal_true;
      assert(bool(e_eval));
      if (is_literal_true(e_eval) || is_literal_false(e_eval)) {
        if (single_case(e_eval)) {
          // If the single case holds, then elt.args has 0 or 1 element
          assert(elt.args.size() <= 1);
          // By default, assume elt.args has no elements
          ret = e.ctx().bool_val(kind == Z3_OP_AND ? false :
                                 true);
          // Finds the single arg, if it's there. For an AND, the expr is false
          // and the single arg is false, too. For an OR, the expr is true and
          // the single arg is true, too. Rewrites to the single arge.
          for (auto& [arg, arg_eval] : elt.args) {
            (void)arg_eval;
            ret = lookup(arg);
            break;
          }
        } else {
          // true AND(x, ....) => x and assumes that all other literals are
          // true. false OR(x, ....) => x and assumes that all other literals
          // are false.
          auto it = elt.args.begin();
          // Rewrites the node to its first arg, which has the same truth value.
          ret = lookup((*it++).first);
          auto maybe_negate = kind == Z3_OP_AND ? expr_id :
              expr_not;
          for (auto ie = elt.args.end(); it != ie; ++it) {
            // Adds predicates of appropriate polarity with maybe_negate
            auto new_arg = lookup((*it).first);
            auto new_pred = maybe_negate(new_arg);
            auto inserted = AddPredicate(new_pred);
            if (inserted)
              logger.Log(6, "{}: ModelJustifier predicate: {}", __LINE__,
                         new_pred);
          }
        }
      } else {
        ret = make_identity_rewriter(NewArgsExprVector(e))(e);
      }
      EUFORIA_EXPENSIVE_ASSERT(z3::eq(Eval(ret), e_eval), "{} != {}",
                               Eval(ret), e_eval);
      return ret;
    }
    
    
    default: {
      auto nn = e.decl()(NewArgsExprVector(e));
      fmt::print(std::cerr, "unsupported node in literal: {}", nn);
      mylog(nn);
      EUFORIA_FATAL("error");
    }
  }
}


template <>
z3::expr ModelJustifier::visitITE(const StackElt& elt) {
  auto& e = elt.node;
  z3::expr ret(e.ctx());
  if (elt.args.size() == 2) {
    auto arg_traversed = elt.args[1].first;
    auto predicate = Arg(e, 0);
    // If the arg traversed is equal to TRUE arg, adds the condition as a
    // predicate. Otherwise adds its negation
    if (z3::eq(arg_traversed, e.arg(1))) {
      ; // do not negate predicate
    } else if (z3::eq(arg_traversed, e.arg(2))) {
      predicate = expr_not(predicate); // negate
    }
    if (AddPredicate(predicate))
      logger.Log(6, "{}: ModelJustifier predicate: {}", __LINE__, predicate);
    ret = lookup(arg_traversed);
    EUFORIA_EXPENSIVE_ASSERT(
        z3::eq(Eval(ret), Eval(e)),
        "{} (before eval: {}) != {} (before eval: {})\n", Eval(ret), ret,
        Eval(e), e);
  } else {
    return make_identity_rewriter(NewArgsExprVector(e))(e);
  }
  return ret;

}

template <>
z3::expr ModelJustifier::visitEQ(const StackElt& elt) {
  auto& e = elt.node;
  z3::expr ret(e.ctx());
  assert(elt.args.size() == 2);
  auto lhs = lookup(elt.args[0].first), rhs = lookup(elt.args[1].first);
  if (lhs.is_bool()) {
    // Due to rewriting, either the lhs or rhs may eval to true but the other
    // may not fully evaluate. So this evals both sides and uses the one which
    // fully evaluates.
    auto lhs_eval = Eval(lhs);
    auto rhs_eval = Eval(rhs);
    auto e_eval = Eval(e);
    z3::expr pred(e.ctx());
    logger.Log(6, "ModelJustifier::visitEQ({}): {} == {} ({} == {})",
               e_eval, lhs, rhs, lhs_eval, rhs_eval);
    if (is_literal_true(e_eval)) {
      // e is true: M |= lhs == rhs
      if (is_literal_false(lhs_eval) || is_literal_false(rhs_eval)) {
      logger.Log(6, "ModelJustifier::visitEQ(true): false==false");
        // M |= !lhs && !rhs
        ret = expr_not(lhs), pred = expr_not(rhs);
      } else {
        assert(is_literal_true(lhs_eval) || is_literal_true(rhs_eval));
      logger.Log(6, "ModelJustifier::visitEQ(true): else");
        // M |= lhs && rhs
        ret = lhs, pred = rhs;
      }
    } else if (is_literal_false(e_eval)) {
      logger.Log(6, "ModelJustifier::visitEQ(false)");
      // e is false: lhs opposite of rhs
      if (is_literal_true(lhs_eval) ||
          is_literal_false(rhs_eval)) {        // M |= lhs & !rhs
        ret = rhs, pred = lhs;
      } else if (is_literal_false(lhs_eval) ||
                 is_literal_true(rhs_eval)) {  // M |= !lhs & rhs
        ret = lhs, pred = rhs;
      } else {
        EUFORIA_ASSERT(
            false,
            "evals neither true nor false\n"
            "lhs: {}\n" "rhs: {}\n" "lhs_eval: {}\n" "rhs_eval: {}\n",
            lhs, rhs, lhs_eval, rhs_eval);
      }
    } else {
      ret = expr_eq(lhs, rhs);
    }
    if (bool(pred)) {
      auto inserted = AddPredicate(pred);
      if (inserted)
        logger.Log(6, "{}: ModelJustifier predicate: {}", __LINE__, pred);
      EUFORIA_ASSERT(
          z3::eq(Eval(ret), Eval(e)),
          "ret eval not equal to original expression e eval\n"
          "e: {}\n" "e eval: {}\n"
          "e.arg(0) eval: {}\n" "e.arg(1) eval: {}\n"
          "lhs: {}\n" "lhs_eval: {}\n" "rhs: {}\n" "rhs_eval: {}\n"
          "ret: {}\n" "ret eval: {}\n"
          "pred: {}\n" "pred eval: {}\n", 
          e, e_eval, Eval(e.arg(0)), Eval(e.arg(1)), lhs, lhs_eval, rhs,
          rhs_eval, ret, Eval(ret), pred, Eval(pred));
    }
  } else {
    ret = expr_eq(lhs, rhs);
  }
  assert(bool(ret));
  EUFORIA_EXPENSIVE_ASSERT(z3::eq(Eval(ret), Eval(e)), "{} != {}", Eval(ret),
                           Eval(e));
  return ret;
}

template <>
z3::expr ModelJustifier::visitDISTINCT(const StackElt& elt) {
  auto& e = elt.node;
  z3::expr ret(e.ctx());
  if (e.arg(0).is_bool()) {
    auto lhs = lookup(elt.args[0].first), rhs = lookup(elt.args[1].first);
    auto lhs_eval = Eval(lhs), rhs_eval = Eval(rhs);
    auto e_eval = Eval(e);
    z3::expr pred(e.ctx());
    if (is_literal_false(e_eval)) {
      // e is false: M |= lhs == rhs.
      if (is_literal_true(lhs_eval) || is_literal_true(rhs_eval)) {
        pred = expr_not(rhs), ret = expr_not(lhs);
      } else {
        pred = rhs, ret = lhs;
      }
    } else {
      // e is true: M |= (!lhs&rhs) | (lhs&!rhs)
      if (is_literal_true(lhs_eval) ||
          is_literal_false(rhs_eval)) {        // M |= lhs & !rhs
        ret = lhs, pred = expr_not(rhs);
      } else if (is_literal_false(lhs_eval) ||
                 is_literal_true(rhs_eval)) {  // M |= !lhs & rhs
        ret = rhs, pred = expr_not(lhs);
      }
    }
    auto inserted = AddPredicate(pred);
    if (inserted)
      logger.Log(6, "{}: ModelJustifier predicate: {}", __LINE__, pred);
    EUFORIA_ASSERT(
        z3::eq(Eval(ret), Eval(e)),
        "ret eval not equal to original expression e eval\n"
        "e: {}\n" "e eval: {}\n"
        "e.arg(0) eval: {}\n" "e.arg(1) eval: {}\n"
        "lhs: {}\n" "lhs_eval: {}\n" "rhs: {}\n" "rhs_eval: {}\n"
        "ret: {}\n" "ret eval: {}\n"
        "pred: {}\n" "pred eval: {}\n", 
        e, e_eval, Eval(e.arg(0)), Eval(e.arg(1)), lhs, lhs_eval, rhs,
        rhs_eval, ret, Eval(ret), pred, Eval(pred));
  } else {
    ret = expr_distinct(NewArgsExprVector(e));
  }
  EUFORIA_EXPENSIVE_ASSERT(z3::eq(Eval(ret), Eval(e)), "{} != {}", Eval(ret),
                           Eval(e));
  return ret;
}

}
