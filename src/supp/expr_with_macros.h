// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_EXPR_WITH_MACROS_H_
#define EUFORIA_SUPP_EXPR_WITH_MACROS_H_

#include <boost/bimap.hpp>

#include "checker_types.h"
#include "supp/expr_graph_traits.h"
#include "supp/expr_supp.h"

namespace euforia {
//! Defines a graph over an expression rooted at root where macros
//! (intermediate definitions) are inlined as iteration proceeds.
template <typename Map>
class ExprWithMacros {
 public:
  ExprWithMacros(const z3::expr& root, Map *m) : root_(m, root) {}

  inline bool operator==(const ExprWithMacros& other) const {
    return root_ == other.root_;
  }

  inline bool operator!=(const ExprWithMacros& other) const {
    return !(*this == other);
  }
  
  //^--------------------------------------------------------------------------^

  class Iterator;
  
  class Node {
    friend class Iterator;
   public:
    Node(Map *defs, const z3::expr& e)
        : defs_(defs), e_(e) {
      if (defs) {
        if (auto search = defs->find(e); search != defs->end()) {
          e_ = search->second;
        }
      }
    }

    Node(const Node& n) : defs_(n.defs_), e_(n.e_) {}

    Node& operator=(const Node& n) {
      defs_ = n.defs_;
      e_ = n.e_;
      return *this;
    }

    inline bool operator==(const Node& other) const {
      return defs_ == other.defs_ && z3::eq(e_, other.e_);
    }

    inline bool operator!=(const Node& other) const {
      return !(*this == other);
    }

    Iterator child_begin();
    Iterator child_end();

    operator z3::expr() const { return e_; }

   private:
    Map *defs_;
    z3::expr e_;
  };

  Node root() const { return root_; }

  //^--------------------------------------------------------------------------^

  class Iterator {
   public:
    Iterator(Node n, ExprArgIterator it)
        : defs_(n.defs_), it_(it) {
    }

    inline bool operator==(const Iterator& other) const {
      return defs_ == other.defs_ && it_ == other.it_;
    }

    inline bool operator!=(const Iterator& other) const {
      return !(*this == other);
    }

    // Uses FindDef to inline the macros
    inline const Node operator*() const { return Node(defs_, *it_); }
    inline Node operator*() { return Node(defs_, *it_); }
    inline Iterator& operator++() { ++it_; return *this; }
    inline Iterator operator++(int) {
      Iterator tmp = *this;
      ++*this;
      return tmp;
    }

   private:
    Map *defs_;
    euforia::ExprArgIterator it_;
  };

 private:
  Node root_;
};


template <typename Map>
typename ExprWithMacros<Map>::Iterator ExprWithMacros<Map>::Node::child_begin() {
  return Iterator(*this, ExprArgIterator::begin(e_));
}

template <typename Map>
typename ExprWithMacros<Map>::Iterator ExprWithMacros<Map>::Node::child_end() {
  return Iterator(*this, ExprArgIterator::end(e_));
}
} // end namespace euforia

namespace llvm {
template <typename Map>
class GraphTraits<euforia::ExprWithMacros<Map>> {
 public:
  using GraphT = euforia::ExprWithMacros<Map>;
  using NodeRef = typename GraphT::Node;
  using ChildIteratorType = typename GraphT::Iterator;

  static NodeRef getEntryNode(const euforia::ExprWithMacros<Map>& g) {
    return g.root();
  }

  static ChildIteratorType child_begin(NodeRef n) {
    return n.child_begin();
  }

  static ChildIteratorType child_end(NodeRef n) {
    return n.child_end();
  }
};
} // end namespace euforia

#endif
