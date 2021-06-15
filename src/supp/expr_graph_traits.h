// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef expr_graph_traits_hpp
#define expr_graph_traits_hpp

#include <boost/range/iterator_range.hpp>
#include <boost/optional.hpp>
#include <llvm/ADT/GraphTraits.h>
#include <z3++.h>

namespace {
template<class T>
class ProxyHolder {
 public:
  ProxyHolder(const T& t) : t_(t) {}
  T* operator->() { return std::addressof(t_); }
 private:
  T t_;
};
}

namespace euforia {
//! Iterator over immediate args of an expression
class ExprArgIterator {
 public:
  using value_type = z3::expr;
  using reference = z3::expr;
  using pointer = z3::expr*;
  using iterator_category = std::input_iterator_tag;
  using difference_type = int;
  
  ExprArgIterator() : i_(0) {}
  ExprArgIterator(const z3::expr& e, unsigned i) : e_(e), i_(i) {}

  // static constructor
  inline static ExprArgIterator begin(const z3::expr& e) {
    return ExprArgIterator(e, 0);
  }

  // static constructor
  inline static ExprArgIterator end(const z3::expr& e) {
    switch (e.kind()) {
      case Z3_QUANTIFIER_AST:
        return ExprArgIterator(e, 1);
      case Z3_APP_AST:
        return ExprArgIterator(e, e.num_args());
      default:
        return ExprArgIterator(e, 0);
    }
  }

  inline bool operator==(const ExprArgIterator& r) const {
    return z3::eq(*e_, *r.e_) && i_ == r.i_;
  }

  inline bool operator!=(const ExprArgIterator& it) const {
    return !(*this == it);
  }

  inline z3::expr operator*() const {
    if (e_->is_quantifier() && i_ == 0) {
      return e_->body();
    } else {
      return e_->arg(i_);
    }
  }
  inline z3::expr operator*() {
    if (e_->is_quantifier() && i_ == 0) {
      return e_->body();
    } else {
      return e_->arg(i_);
    }
  }
  inline ExprArgIterator& operator++() { ++i_; return *this; }
  
  inline ExprArgIterator operator++(int) {
    ExprArgIterator tmp = *this; ++*this; return tmp;
  }

  ProxyHolder<value_type> operator->() const {
    return ProxyHolder<value_type>(**this);
  }

 private:
  boost::optional<z3::expr> e_;
  unsigned i_;
};

static auto ExprArgs(const z3::expr& e) {
  return boost::make_iterator_range(
      ExprArgIterator::begin(e), ExprArgIterator::end(e));
}
} // end namespace euforia

//^----------------------------------------------------------------------------^

namespace llvm {
template <>
class GraphTraits<z3::expr> {
 public:
  using NodeRef = z3::expr;
  using ChildIteratorType = euforia::ExprArgIterator;

  static NodeRef getEntryNode(const z3::expr& e) { return e; }

  static ChildIteratorType child_begin(NodeRef n) {
    return euforia::ExprArgIterator::begin(n);
  }
  static ChildIteratorType child_end(NodeRef n) {
    return euforia::ExprArgIterator::end(n);
  }
};
} // end namespace llvm

#endif
