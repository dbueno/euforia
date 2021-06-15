// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_EXPR_NORMALIZE_H_
#define EUFORIA_SUPP_EXPR_NORMALIZE_H_

#include <z3++.h>
#include <vector>

#include "supp/expr_rewriter.h"
#include "supp/expr_supp.h"

namespace euforia {
// Normalizes an expressio by normalizing argument order. Sorts the arguments
// to any commutative operator by their hashes.
class ExprNormalize : public ExprRewriter<ExprNormalize> {
 public:
  z3::expr operator()(const z3::expr& e) {
    return Rewrite(e);
  }

  z3::expr visit(const z3::expr& e) {
    switch (e.decl().decl_kind()) {
      case Z3_OP_AND:
      case Z3_OP_OR:
      case Z3_OP_BADD:
      case Z3_OP_BMUL:
      case Z3_OP_ADD:
      case Z3_OP_MUL:
      case Z3_OP_EQ:
      case Z3_OP_DISTINCT: {
        // Sorts arguments then creates new node with them
        std::vector<z3::expr> args; 
        args.reserve(e.num_args());
        copy_args(e, std::back_inserter(args));
        auto cmp = [](const z3::expr& a, const z3::expr& b) {
          return z3::CompareExpr()(a, b);
        };
        std::sort(args.begin(), args.end(), cmp);
        z3::expr_vector new_args(e.ctx());
        copy(args.begin(), args.end(), ExprVectorInserter(new_args));
        return e.decl()(new_args);
      }

      default:
        return e.decl()(NewArgsExprVector(e));
    }
  }
};
} // namespace euforia

#endif
