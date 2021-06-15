// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_REWRITER_H_
#define EUFORIA_SUPP_REWRITER_H_

#include <llvm/ADT/PostOrderIterator.h>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>

namespace euforia {
template <typename SubClass, typename NodeRef, typename Ret,
         typename Set, typename Cache>
class Rewriter;
}

namespace llvm {
template <typename SubClass, typename NodeRef, typename Ret,
         typename Set, typename Cache>
class po_iterator_storage<euforia::Rewriter<
    SubClass, NodeRef, Ret, Set, Cache>, true> {
 public:
  inline po_iterator_storage(
      euforia::Rewriter<SubClass, NodeRef, Ret, Set, Cache>& s)
      : rw_(s) {}

  // Defined below
  void finishPostorder(NodeRef e);
  bool insertEdge(Optional<NodeRef> from, NodeRef to);

 private:
  euforia::Rewriter<SubClass, NodeRef, Ret, Set, Cache>& rw_;
};
}

namespace euforia {
//!
//! Rewriter for DAGs. Calls SubClass::visit to rewrite each node. Nodes that
//! have been rewritten can be accessed with lookup().
//!
//! \param SubClass - cocrete subclass, crtp style
//!
//! \param GraphT - there is a graph traits for this
//!
//! \param Ret - rewriter returns this type
//!
//! \param Set - for stored visited nodes
//!
//! \param Cache - for caching intermediate rewrites
template <typename SubClass, typename GraphT,
          typename Ret=typename llvm::GraphTraits<GraphT>::NodeRef,
          typename Set=std::unordered_set<
              typename llvm::GraphTraits<GraphT>::NodeRef>,
          typename Cache=std::unordered_map<
              typename llvm::GraphTraits<GraphT>::NodeRef, Ret>>
class Rewriter {
 public:
  using NodeRef = typename llvm::GraphTraits<GraphT>::NodeRef;
  
  using RewriteIterator = llvm::po_ext_iterator<NodeRef, 
        Rewriter<SubClass, NodeRef, Ret, Set, Cache>>;
  
  inline int64_t num_visits() const { return num_visits_; }
  inline void set_num_visits(unsigned n = 0) { num_visits_ = n; }

  Ret Rewrite(NodeRef n) {
    for (auto it = static_cast<SubClass*>(this)->rewrite_begin(n),
         ie = static_cast<SubClass*>(this)->rewrite_end(n); it != ie; ++it) {
      ++num_visits_;
      auto ret = static_cast<SubClass*>(this)->visit(*it);
      cache_.insert({static_cast<SubClass*>(this)->get_rewrite_node(*it), ret});
    }
    return lookup(n);
  }

  //! Can be defined in a subclass if the iterator type is custom
  inline NodeRef get_rewrite_node(NodeRef n) const {
    return n;
  }

  inline const Ret& lookup(NodeRef n) const {
    return cache_.at(n);
  }
  inline const Ret& Lookup(NodeRef n) const {
    return lookup(n);
  }
  inline bool is_in_cache(NodeRef e) const {
    return cache_.find(e) != cache_.end();
  }
  Cache& cache() { return cache_; }
  const Cache& cache() const { return cache_; }
  
  inline void Reset() {
    visited_.clear();
    cache_.clear();
    num_visits_ = 0;
  }
  
  //! iterate in rewrite order over e
  inline RewriteIterator rewrite_begin(NodeRef e) {
    return llvm::po_ext_begin(e, *this);
  }

  inline RewriteIterator rewrite_end(NodeRef e) {
    return llvm::po_ext_end(e, *this);
  }
  
  inline void FinishPostorder(NodeRef) {}

  inline bool VisitPreorder(const llvm::Optional<NodeRef>& from, NodeRef to) {
    bool b = false;
    if (cache_.find(to) == cache_.end()) {
      b = llvm::po_iterator_storage<Set, true>(visited_).insertEdge(from,
                                                                      to);
    }
    return b;
  }

 protected:
  Set visited_;
  Cache cache_;
  int64_t num_visits_;
  
  template <typename... Args>
  Rewriter(Args&&... args) 
      : visited_(std::forward<Args>(args)...), num_visits_(0) {}
  // XXX I don't know why I deleted this
  Rewriter(const Rewriter&) = delete;
  ~Rewriter() = default;
};
}

namespace llvm {
template <typename SubClass, typename NodeRef, typename Ret,
         typename Set, typename Cache>
inline void llvm::po_iterator_storage<euforia::Rewriter<
    SubClass, NodeRef, Ret, Set, Cache>, true>::finishPostorder(NodeRef e) {
  rw_.FinishPostorder(e);
}

template <typename SubClass, typename NodeRef, typename Ret,
         typename Set, typename Cache>
inline bool llvm::po_iterator_storage<euforia::Rewriter<
    SubClass, NodeRef, Ret, Set, Cache>, true>::insertEdge(
        Optional<NodeRef> from, NodeRef to) {
  return rw_.VisitPreorder(from, to);
}

}

#endif
