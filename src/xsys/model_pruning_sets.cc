// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "xsys/model_pruning_sets.h"

#include "abstract_model.h"
#include "supp/std_supp.h"

using namespace llvm;

namespace euforia {

bool ModelPruningTraversal::VisitEdge(
    const llvm::Optional<ExprWithDefBimap::Node>& From,
    const ExprWithDefBimap::Node& To_in) {
  const z3::expr& To = To_in;
  std::stringstream ss;
  if (From) {
    const z3::expr& e = *From;
    fmt::print(ss, "{:08x}", e.hash());
  }
  logger.Log(7, "ModelPruningTraversal::VisitEdge {} -> {:08x}", ss.str(),
             To.hash());

  if (!insert_edge_(From, To_in)) {
    return false;
  }

  //if (set_.preorder_visit != nullptr) {
  //  set_.preorder_visit(To);
  //}
  if (From && nodes_.find(To) == nodes_.end()) {
    auto& eval = eval_;
    const z3::expr& top = *From;
    bool found_child = false;
    auto child_search = unique_child_.find(top);
    found_child = child_search != unique_child_.end();
    // If we have found_child, then we've seen top before for at least one edge
    // and we found the unique child that needed to be followed. We don't want
    // to do that again.
    // if (found_child && !z3::eq(To, child_search->second)) {
    //   return false;
    // }
    switch (top.decl().decl_kind()) {
      case Z3_OP_ITE: {
        // Skip examining the false branch of ITE
        // Can skip adding this edge if it is (1) not pointing at the
        // condition and (2) not pointing at the true branch
        if (found_child && !z3::eq(child_search->second, To)) {
          return false;
        }
        auto cond = arg_with_def(top, 0);
        if (!z3::eq(cond, To)) { // (1)
          const auto test = eval(cond, false);
          assert(is_literal_true(test) || is_literal_false(test));
          auto true_branch = arg_with_def(top, is_literal_true(test) ? 1 : 2 );
          unique_child_.insert({top, true_branch});
          if (!z3::eq(To, true_branch)) // (2)
            return false;
        }
      }
      break;

      case Z3_OP_OR: {
        if (found_child && !z3::eq(child_search->second, To)) {
          return false;
        }
        // XXX use eval_top instead of calling eval again
        auto eval_top = eval(top, false);
        assert(is_literal_true(eval_top) || is_literal_false(eval_top));
        if (is_literal_true(eval(top, false))) {
          // Find true child and only expand that node
          bool found = false;
          for (unsigned i = 0; i < top.num_args(); i++) {
            auto arg = arg_with_def(top, i);
            if (is_literal_true(eval(arg, false))) {
              found = true;
              unique_child_.insert({top, arg});
              if (!z3::eq(arg, To)) {
                return false;
              }
              break;
            }
          }
          // The OR can eval to true without any kid eval'ing to true. If this
          // happens, it's due to the OR being a tautology under a particular
          // model. In that case, we should traverse NONE of the children.
          if (!found)
            return false;
        }
      }
      break;
      
      case Z3_OP_AND: {
        if (found_child && !z3::eq(child_search->second, To)) {
          return false;
        }
        // XXX use eval_top instead of calling eval again
        auto eval_top = eval(top, false);
        assert(is_literal_true(eval_top) || is_literal_false(eval_top));
        if (is_literal_false(eval(top, false))) {
          bool found = false;
          // Find false child and only expand that node
          for (unsigned i = 0; i < top.num_args(); i++) {
            auto arg = arg_with_def(top, i);
            if (is_literal_false(eval(arg, false))) {
              found = true;
              unique_child_.insert({top, arg});
              if (!z3::eq(arg, To)) {
                return false;
              }
              break;
            }
          }
          // Similar to OR case. The AND is tautologically false (e.g., (and b
          // (not b)), so don't explore any children.
          if (!found)
            return false;
        }
      }
      break;

      default:
        ;
    }
  }
  logger.Log(7, "{:08x} is {}in nodes", To.hash(),
             nodes_.find(To) == nodes_.end() ? "not " : "");
  return nodes_.insert(To).second;
}

}
