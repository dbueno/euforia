// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef expr_rewriter_hpp
#define expr_rewriter_hpp

#include <boost/range/iterator_range.hpp>
#include <vector>
#include <z3++.h>

#include "supp/expr_graph_traits.h"
#include "supp/expr_supp.h" // expr_umap
#include "supp/rewriter.h"




//^----------------------------------------------------------------------------^
// rewriter

namespace euforia {


//! This class allows one to use a custom visited set. This can make many
//! different traversals relatively straightforward to implement. Or at least
//! modular.
template <typename SubClass,
         // Rewriter returns this type
         typename Ret=z3::expr,
         // What holds visited nodes
         typename Set=ExprSet>
class ExprRewriter : public Rewriter<SubClass, z3::expr, Ret, Set,
    ExprMap<Ret>> {
 public:
  using RewriterT = euforia::Rewriter<SubClass, z3::expr, Ret, Set,
        ExprMap<Ret>>;

  // using RewriterT::Rewrite;
  // using RewriterT::Lookup;
  using RewriterT::lookup;
  // using RewriterT::VisitAndCache;
  // using RewriterT::num_visits;
  // using RewriterT::set_num_visits;
  // using RewriterT::rewrite_begin;
  // using RewriterT::rewrite_end;

 protected:
  using RewriterT::cache_;

  //! constructor passes args to the custom set type
  template <typename... Args>
  ExprRewriter(Args&&... args) 
      : RewriterT(std::forward<Args>(args)...) {}
  // XXX I don't know why I deleted these.
  ExprRewriter(const ExprRewriter&) = delete;
  ExprRewriter& operator=(const ExprRewriter&) = delete;
  ~ExprRewriter() = default;
  
  // XXX rename to arg
  inline Ret Arg(const z3::expr& e, unsigned i) const {
    return lookup(e.arg(i));
  }
  inline Ret arg(const z3::expr& e, unsigned i) const {
    return lookup(e.arg(i));
  }

  //! Copies rewritten arguments of e in order to the output iterator
  template <class OutputIt>
  void copy_args(const z3::expr& e, OutputIt out) const {
    copy(args_begin(e), args_end(e), out);
  }
  
  // XXX rename to new_args_expr_vector
  inline z3::expr_vector NewArgsExprVector(const z3::expr& e) const {
    z3::expr_vector args(e.ctx());
    copy_args(e, ExprVectorInserter(args));
    return args;
  }

  //! Iterates over args in the cache
  template <typename Cache>
  class CachedArgIterator {
   public:
    using difference_type = std::ptrdiff_t;
    using value_type = Ret;
    using reference = const Ret&;
    using pointer = const Ret*;
    using iterator_category = std::forward_iterator_tag;

    CachedArgIterator(const Cache& c, ExprArgIterator it) 
        : cache_(c), it_(it) {}

    bool operator==(const CachedArgIterator& other) {
      return &cache_ == &other.cache_ && it_ == other.it_;
    }

    bool operator!=(const CachedArgIterator& other) {
      return !(*this == other);
    }

    reference operator*() const {
      return cache_.at(*it_);
    }

    CachedArgIterator& operator++() { // preincrement
      ++it_;
      return *this;
    }
    
    CachedArgIterator operator++(int) { // postincrement
      CachedArgIterator tmp = *this;
      ++*this;
      return tmp;
    }
    
   private:
    const Cache& cache_;
    ExprArgIterator it_;
  };

  using ArgIterator = CachedArgIterator<ExprMap<Ret>>;

  //! iterate over rewritten args of e, in order
  ArgIterator args_begin(const z3::expr& e) const {
    return ArgIterator(cache_, ExprArgIterator::begin(e));
  }
  
  ArgIterator args_end(const z3::expr& e) const {
    return ArgIterator(cache_, ExprArgIterator::end(e));
  }

  auto args(const z3::expr& e) const {
    return boost::make_iterator_range(args_begin(e), args_end(e));
  }
};

}

#endif /* rewriter_hpp */
