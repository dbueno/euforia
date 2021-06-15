// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef expr_substitution_hpp
#define expr_substitution_hpp

#include "supp/expr_iterators.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_visitor.h"

#include <z3++.h>

namespace euforia {

class ExprSubstitution {
  z3::expr_vector src_, dst_;
 public:

  explicit ExprSubstitution(z3::context& ctx) : src_(ctx), dst_(ctx) {}
  ExprSubstitution(const z3::expr_vector& src,
                   const z3::expr_vector& dst) : src_(src), dst_(dst) {}
  ExprSubstitution(const ExprSubstitution& other);

  z3::context& ctx();

  inline const z3::expr_vector& src() const { return src_; }
  inline const z3::expr_vector& dst() const { return dst_; }

  unsigned size() const { return src_.size(); }

  void Clear();
  
  //! Adds [eold / enew] to what will be substituted.
  void AddSubstitution(const z3::expr& eold, const z3::expr& enew);

  template <typename T>
  void AddSubstitution(const T& src, const T& dst) {
    for (auto it_src = src.begin(), ie_src = src.end(),
         it_dst = dst.begin(), ie_dst = dst.end();
         it_src != ie_src && it_dst != ie_dst;
         ++it_src, ++it_dst) {
      AddSubstitution(*it_src, *it_dst);
    }
  }
  
  //! Performs substitution on e
  z3::expr operator()(const z3::expr& e) const;

  //! Parallel composition
  ExprSubstitution operator&(const ExprSubstitution& other) const;

  //! Returns the inverse substitution. The inverse substitution is defined if
  //! this substitution is 1-1.
  ExprSubstitution inverse() const {
    return ExprSubstitution(dst_, src_);
  }

  // overrides
  
  void Print(std::ostream& out) const;
  
};

std::ostream& operator<<(std::ostream&, const ExprSubstitution&);

//^----------------------------------------------------------------------------^

class CachingExprSubstitution : public ExprRewriter<CachingExprSubstitution>,
    public ExprVisitor<CachingExprSubstitution, z3::expr> {
 public:
  explicit CachingExprSubstitution(z3::context& c) : src_(c), dst_(c) {}

  z3::context& ctx() { return src_.ctx(); }

  void Clear();

  //! substitute eold for enew
  void AddSubstitution(const z3::expr& eold, const z3::expr& enew);

  //! substitute
  z3::expr operator()(const z3::expr& e);

  // overrides
  z3::expr visitExpr(const z3::expr& e);
  z3::expr visitUNINTERPRETED(const z3::expr&);

 private:
  z3::expr_vector src_, dst_;
  
  using ExprRewriter::Rewrite;
};

}

#endif
