// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef model_simplifying_visited_set_hpp
#define model_simplifying_visited_set_hpp

#include <z3++.h>
#include <memory>

#include "supp/expr_def_bimap.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_supp.h"
#include "supp/expr_with_macros.h"
#include "supp/std_supp.h"

namespace euforia {
class ModelPruningTraversal;
using ExprWithDefBimap = ExprWithMacros<ExprDefBimap::left_map>;
}

namespace llvm {
template <>
class po_iterator_storage<euforia::ModelPruningTraversal, true> {
 public:
  po_iterator_storage(euforia::ModelPruningTraversal& tct) : traversal_(tct) {}

  // Defined below
  bool insertEdge(Optional<euforia::ExprWithDefBimap::Node>,
                  euforia::ExprWithDefBimap::Node);
  bool insertEdge(Optional<z3::expr>, z3::expr);
  void finishPostorder(euforia::ExprWithDefBimap::Node);

 private:
  euforia::ModelPruningTraversal& traversal_;
};

}

namespace euforia {
//! Traverses the nodes in an expression, but doesn't traverse those that
//! didn't matter to the model. Specifically, (1) when an ITE is encountered
//! only the true branch is traversed; (2) when a true OR is encountered it
//! only traverses the first true child; (3) when a false AND is encountered,
//! only traverses the first false child.
//!
//! This class supports a formula that contains macros -- definitions that are
//! automatically expanded as we traverse the formula. You specify them using
//! the map defs_. This feature makes it possible to Tseitin-convert a formula,
//! for example, then traverse just the parts the model needs while ignoring
//! the Tseitin variables.
class ModelPruningTraversal {
 public:
  using ModelPruningIterator =
      llvm::po_iterator<ExprWithDefBimap, ModelPruningTraversal, true>;
  
  using InsertEdgeFunc = std::function<bool(
      const llvm::Optional<euforia::ExprWithDefBimap::Node>& from,
      const euforia::ExprWithDefBimap::Node& to)>;

  ModelPruningTraversal(Z3EvalFunc eval, ExprDefBimap *defs = nullptr)
      : eval_(eval), defs_(defs),
      insert_edge_([](auto&&, auto&&) { return true; }) {}

  //! The function set here is invoked before deciding whether to visit a given
  //! edge. If it returns false, the edge won't be visited. If it returns true,
  //! then this traversal will decide whether the edge needs to be pruned.
  //!
  //! This can be used as a pre-filter on edges; note that it can't really look
  //! into the visited set (nodes_). It's used by the ModelJustifier to see if
  //! the target of the edge is in the cache, and if so, it isn't visited
  //! again.
  void set_insert_edge(InsertEdgeFunc f) { insert_edge_ = f; }

  ModelPruningIterator begin(const z3::expr& e) {
    return llvm::po_ext_begin(
        ExprWithDefBimap(e, defs_ ? &defs_->left : nullptr), *this);
  }

  ModelPruningIterator end(const z3::expr& e) {
    return llvm::po_ext_end(
        ExprWithDefBimap(e, defs_ ? &defs_->left : nullptr), *this);
  }

  // Called by po_iterator when an edge from an expression is being expanded
  bool VisitEdge(const llvm::Optional<euforia::ExprWithDefBimap::Node>& from,
                 const euforia::ExprWithDefBimap::Node& to);

  // This method is so that we can lift z3::exprs into our annotated versions
  // that support (but don't require) expanding macros
  inline bool VisitEdge(const llvm::Optional<z3::expr>& from,
                        const z3::expr& to) {
    llvm::Optional<ExprWithDefBimap::Node> from_node;
    if (from) {
      from_node = ExprWithDefBimap::Node(&defs_->left, *from);
    }
    return VisitEdge(from_node, ExprWithDefBimap::Node(&defs_->left, to));
  }

  inline void FinishPostorder(const z3::expr&) {}

  // Returns the i'th argument of e, but using a def if there is one. Used by
  // VisitEdge to make sure it queries appropriate child nodes.
  z3::expr arg_with_def(const z3::expr& e, unsigned i) const {
    auto r = e.arg(i);
    if (defs_) {
      if (auto search = defs_->left.find(r); search != defs_->left.end()) {
        r = search->second;
      }
    }
    return r;
  }

 private:
  Z3EvalFunc eval_;
  ExprSet nodes_;      // set of nodes visited
  ExprDefBimap *defs_; // macro definitions
  // called as a pre-filter on edges
  InsertEdgeFunc insert_edge_;
  ExprMap<z3::expr> unique_child_;
};
}


//*-------------------------------------------------------------------------------*
//

inline bool llvm::po_iterator_storage<euforia::ModelPruningTraversal,
    true>::insertEdge(Optional<euforia::ExprWithDefBimap::Node> From,
                      euforia::ExprWithDefBimap::Node To) {
  return traversal_.VisitEdge(From, To);
}

inline bool llvm::po_iterator_storage<euforia::ModelPruningTraversal,
    true>::insertEdge(Optional<z3::expr> From,
                      z3::expr To) {
  return traversal_.VisitEdge(From, To);
}

inline void llvm::po_iterator_storage<euforia::ModelPruningTraversal,
    true>::finishPostorder(euforia::ExprWithDefBimap::Node e) {
  return traversal_.FinishPostorder(e);
}

#endif
