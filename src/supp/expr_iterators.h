// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef expr_iterators_hpp__
#define expr_iterators_hpp__

#include "supp/expr_supp.h"
#include "expr_graph_traits.h"

#include <boost/range.hpp>
#include <boost/range/iterator_range.hpp>
#include <deque>
#include <llvm/ADT/DepthFirstIterator.h>
#include <llvm/ADT/PostOrderIterator.h>


namespace std {
// Specialize directly becasue my z3 doesn't do it sigh
template <>
struct iterator_traits<z3::expr_vector::iterator> {
  using iterator_category = forward_iterator_tag;
  using value_type = z3::expr;
  using reference = value_type;
  using pointer = value_type*;
  using difference_type = unsigned;
};
} // end namespace std

namespace euforia {
//^----------------------------------------------------------------------------^
// iterators that walk the expr dag
  
struct IterExprSet {
  ExprSet V;
  using iterator = ExprSet::iterator;
  std::pair<iterator,bool> insert(z3::expr e) { return V.insert(e); }
  void completed(z3::expr) {}
};

// Warning: df_expr_iterator was found to be really, really slow under an
// Ubuntu 16.04 linux machine I had. With clang 8. I don't know why. The weird
// part is that df_expr_ext_iterator using IterExprSet -- which should be
// identical to df_expr_iterator -- was much, much faster. *shrug*
//
// This behavior is likely due to the fact that copying this iterator is very
// heavyweight, especially if you're doing it in a loop (e.g., with a
// post-increment). It appears that the standard c++ library assumes iterators
// are *cheap* to copy. LLVM's documentation says to prefer pre-increment
// because many iterators are *expensive* to copy. In any case, we'll prefer
// iterators with *external storage* so this problem doesn't come up very
// often. At least if we can.
using df_expr_iterator     = llvm::df_iterator<z3::expr, IterExprSet>;
using df_expr_ext_iterator = llvm::df_ext_iterator<z3::expr, IterExprSet>;
using po_expr_iterator     = llvm::po_iterator<z3::expr, ExprSet>;
using po_expr_ext_iterator = llvm::po_ext_iterator<z3::expr, ExprSet>;

//! Iterator over all the expressions rooted at e
//!
//!   z3::expr e = ...;
//!   for (auto& d : ExprDescendents(e)) { ... use descendent d of e }
static inline auto ExprDescendents(const z3::expr& e) {
  return boost::iterator_range<po_expr_iterator>(
      po_expr_iterator::begin(e), po_expr_iterator::end(e));
}


//^----------------------------------------------------------------------------^

//! Iterator over all subexpressions of the same kind nested at the top level
class ExprFlatKindIterator {
 public:
  using value_type = const z3::expr;
  using difference_type = unsigned;
  using reference = value_type;
  using pointer = value_type*;
  using iterator_category = std::input_iterator_tag;

  inline static ExprFlatKindIterator begin(const z3::expr& e,
                                           Z3_decl_kind kind) {
    return ExprFlatKindIterator(e, kind);
  }

  inline static ExprFlatKindIterator end() {
    return ExprFlatKindIterator();
  }

  inline bool operator==(const ExprFlatKindIterator& it) {
    return queue_ == it.queue_;
  }

  inline bool operator!=(const ExprFlatKindIterator& it) {
    return !(*this == it);
  }

  inline ExprFlatKindIterator& operator++() {
    queue_.pop_back();
    Advance();
    return *this;
  }

  ExprFlatKindIterator operator++(int) {
    ExprFlatKindIterator copy(*this);
    Advance();
    return copy;
  }

  inline value_type operator*() const {
    return queue_.back();
  }

  inline ProxyHolder<value_type> operator->() const {
    return ProxyHolder<value_type>(**this);
  }

 private:
  inline explicit ExprFlatKindIterator(const z3::ExprWrapper& e,
                                       Z3_decl_kind kind)
      : queue_({e}), kind_(kind) {
    Advance();
  }
  
  inline ExprFlatKindIterator() {}

  void Advance() {
    while (!queue_.empty()) {
      const z3::expr& back = queue_.back();
      if (back.is_app() && back.decl().decl_kind() == kind_) {
        queue_.pop_back();
        for (unsigned i = 0; i < back.num_args(); i++) {
          queue_.push_front(back.arg(i));
        }
      } else {
        break; // back() is not an and
      }
    }
  }

  // invariant is that the f the queue is nonempty, queue's back() element is
  // not an or()
  std::deque<z3::ExprWrapper> queue_;
  Z3_decl_kind kind_;
};

//^----------------------------------------------------------------------------^

//! Iterator over all subexpressions that are conjoined at the toplevel
class ExprConjunctIterator {
 public:
  inline static auto begin(const z3::expr& e) {
    return ExprFlatKindIterator::begin(e, Z3_OP_AND);
  }

  inline static auto end() {
    return ExprFlatKindIterator::end();
  }
};

//! for (auto& conjunct : ExprConjuncts(e)) { ... }
static inline auto ExprConjuncts(const z3::expr& e) {
  return boost::iterator_range<ExprFlatKindIterator>(
      ExprConjunctIterator::begin(e), ExprConjunctIterator::end());
}

//^----------------------------------------------------------------------------^

//! Iterator over all subexpressions that are or'd at the toplevel
class ExprDisjunctIterator {
 public:
  inline static auto begin(const z3::expr& e) {
    return ExprFlatKindIterator::begin(e, Z3_OP_OR);
  }

  inline static auto end() {
    return ExprFlatKindIterator::end();
  }
};


//! for (auto& disjunct : ExprDisjuncts(e)) { ... }
static inline auto ExprDisjuncts(const z3::expr& e) {
  return boost::iterator_range<ExprFlatKindIterator>(
      ExprDisjunctIterator::begin(e), ExprDisjunctIterator::end());
}
} // end namespace euforia

//^----------------------------------------------------------------------------^

// boost range support for expr_vector
namespace z3 {
static z3::expr_vector::iterator range_begin(z3::expr_vector& v) {
  return v.begin();
}

static z3::expr_vector::iterator range_begin(const z3::expr_vector& v) {
  return v.begin();
}

static z3::expr_vector::iterator range_end(z3::expr_vector& v) {
  return v.end();
}

static z3::expr_vector::iterator range_end(const z3::expr_vector& v) {
  return v.end();
}
} // end namespace z3

namespace boost {
template <>
struct range_mutable_iterator<z3::expr_vector> {
  using type = z3::expr_vector::iterator;
};

template <>
struct range_const_iterator<z3::expr_vector> {
  using type = z3::expr_vector::iterator;
};
}



#endif
