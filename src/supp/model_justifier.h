// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_MODEL_JUSTIFIER_H_
#define EUFORIA_SUPP_MODEL_JUSTIFIER_H_

#include "checker_types.h"
#include "supp/debug.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_supp.h"
#include "supp/expr_visitor.h"
#include "supp/expr_with_macros.h"
#include "xsys/model_pruning_traversal.h"


namespace euforia {

template <class Pruner>
class ModelJustifierT
    : public ExprRewriter<ModelJustifierT<Pruner>, z3::expr, ExprSet>,
      public ExprVisitor<ModelJustifierT<Pruner>, z3::expr,
                         typename Pruner::StackElt> {
 public:
  using StackElt = typename Pruner::StackElt;
  using Rewriter = ExprRewriter<ModelJustifierT<Pruner>>;
  using Visitor = ExprVisitor<ModelJustifierT<Pruner>, z3::expr,
                              typename Pruner::StackElt>;

  using Rewriter::visited_;
  using Rewriter::cache_;
  using Rewriter::Arg;
  using Visitor::visit;

  ModelJustifierT(Z3EvalFunc eval)
      : Rewriter(), mpt_(eval), predicates_(nullptr) {}

  // Compute the predicates that justify the model on the set of terms
  template <typename InputIt>
  void ComputePredicates(InputIt it, InputIt ie, ExprSet *out) {
    assert(out);
    predicates_ = out;
    for (; it != ie; ++it) {
      auto elt = *it;
      logger.Log(6, "begin ComputePredicates:");
      logger.Log(6, "{}", elt);
      auto ret = Rewrite(elt);
      if (ret.is_bool()) {
        bool inserted = false;
        if (is_literal_true(Eval(ret))) {
          inserted = AddPredicate(ret);
        } else {
          EUFORIA_ASSERT(is_literal_false(Eval(ret)),
                         "ret is {}\n"
                         "Eval(ret) is {}\n", ret, Eval(ret));
          inserted = AddPredicate(expr_not(ret));
        }
        if (inserted)
          logger.Log(6, "{}: ModelJustifier predicate: {}", __LINE__, ret);
      }
    }
  }

  void ComputePredicates(const z3::expr& e, ExprSet *out) {
    auto preds = {e};
    return ComputePredicates(begin(preds), end(preds), out);
  }

  // Simplify the formula as much as possible & find predicates. Returned
  // formula might still be complicated.
  z3::expr Simplify(const z3::expr& e, ExprSet *out) {
    predicates_ = out;
    auto ret = Rewrite(e);
    return ret;
  }

  // overrides for ExprRewriter
  z3::expr get_visit_node(const StackElt& elt) const {
    return elt.node;
  }

  // overrides for Rewriter
  z3::expr get_rewrite_node(const StackElt& elt) const {
    return elt.node;
  }

  inline auto rewrite_begin(z3::expr e) {
    return mpt_.begin(e, visited_);
  }
  
  inline auto rewrite_end(z3::expr e) {
    return mpt_.end(e, visited_);
  }

  // overrides for ExprVisitor
  z3::expr visitExpr(const StackElt&);
  z3::expr visitITE(const StackElt&);
  z3::expr visitEQ(const StackElt&);
  z3::expr visitDISTINCT(const StackElt&);
  z3::expr visitNOT(const StackElt& e) { return expr_not(Arg(e.node,0)); }
  z3::expr visitIMPLIES(const StackElt& e) {
    return Rewrite(expr_or(expr_not(Arg(e.node,0)), Arg(e.node,1)));
  }
  z3::expr visitIFF(const StackElt&) {
    EUFORIA_FATAL("should have been rewritten");
  }

 private:
  ExprSet *predicates_;
  Pruner mpt_;

  z3::expr Rewrite(const z3::expr& e) {
    for (auto it = rewrite_begin(e), ie = rewrite_end(e); it != ie; ++it) {
      cache_.insert({get_visit_node(*it), visit(*it)});
    }
    return cache_.at(e);
  }

  z3::expr Eval(const StackElt&);
  z3::expr Eval(const z3::expr& e) {
    return mpt_.Eval(e, false);
  }

  bool AddPredicate(const z3::expr&);
};

using ModelJustifier = ModelJustifierT<ModelPruningTraversalT>;

}

#endif
