// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/nnf_rewriter.h"

#include <algorithm>
#include <boost/range/algorithm/transform.hpp>

#include "supp/expr_iterators.h"

using namespace std;

namespace euforia {
NnfRewriter::NnfRewriter() {}

z3::expr NnfRewriter::operator()(const z3::expr& e) { return Rewrite(e); }

z3::expr NnfRewriter::visitExpr(const z3::expr& e) {
  return e.decl()(NewArgsExprVector(e));
}

z3::expr NnfRewriter::visitNOT(const z3::expr& e) {
  z3::expr e_new(e.ctx());
  auto arg = Arg(e, 0);
  switch (arg.decl().decl_kind()) {
    case Z3_OP_AND: {
      z3::expr_vector disjuncts(e.ctx());
      boost::transform(ExprConjuncts(arg), ExprVectorInserter(disjuncts),
                       expr_not);
      e_new = expr_mk_or(disjuncts);
      break;
    }

    case Z3_OP_OR: {
      z3::expr_vector conjuncts(e.ctx());
      boost::transform(ExprDisjuncts(arg), ExprVectorInserter(conjuncts),
                       expr_not);
      e_new = expr_mk_and(conjuncts);
      break;
    }

    case Z3_OP_XOR:
      e_new = expr_not(Arg(arg, 0));
      for (auto it = ExprFlatKindIterator::begin(arg, Z3_OP_XOR),
           ie = ExprFlatKindIterator::end(Z3_OP_XOR); it != ie; ++it) {
        e_new = e_new ^ *it;
      }
      break;

    case Z3_OP_EQ:
      assert(arg.num_args() == 2);
      e_new = expr_distinct(Arg(arg, 0), Arg(arg, 1));
      break;

    case Z3_OP_DISTINCT:
      if (arg.num_args() == 2) {
        e_new = expr_eq(Arg(arg, 0), Arg(arg, 1));
        break;
      } else {
        e_new = expr_not(arg); // default
        break;
      }

    case Z3_OP_ITE:
      e_new = z3::ite(Arg(arg, 0), expr_not(Arg(arg, 1)),
                      expr_not(Arg(arg, 2)));
      break;

    default:
      e_new = expr_not(arg);
      break;
  }
  return e_new;
}
} // end namespace euforia
