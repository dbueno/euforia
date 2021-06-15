// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_EQUALITY_LITERAL_H_
#define EUFORIA_SUPP_EQUALITY_LITERAL_H_

#include <z3++.h>

namespace euforia {
//! Breaks down an equality literal into lhs (a variable) and rhs
//!
//! \code
//!   if (EqualityLiteral eq_lit(e); eq_lit.is_equality()) {
//! \endcode
//! or
//! \code
//! if (EqualityLiteral::is_equality(e)) {
//!   EqualityLiteral eq_lit(e);
//!   // process eq_lit.rhs()
//!   // eq_lit.lhs()
//! }
//! \endcode
class EqualityLiteral {
 public:
  explicit EqualityLiteral(const z3::expr& e) : lhs_(e.ctx()), rhs_(e.ctx()) {
    Init(e);
  }

  //! Initialize with given expression. Check is_equality() afterward before
  //! using lhs() and rhs() 
  void Init(const z3::expr& e) {
    // b - Booleans are equalities like (b = true)
    // (not b) - equalities like (b = false)
    // (<var> = <thing>) the obvious one
    // The only ambiguity is <var> = <var>; we let the client take care of that
    // for now.
    if ((is_equality_ = EqualityLiteral::is_equality(e))) {
      if (e.num_args() == 0) { // treat b as (b = true)
        lhs_ = e, rhs_ = e.ctx().bool_val(true);
      } else if (is_not(e)) { // treat (not x) as (x = false)
        lhs_ = e.arg(0), rhs_ = e.ctx().bool_val(false);
      } else {
        lhs_ = e.arg(0), rhs_ = e.arg(1);
        if (lhs_.num_args() != 0) {
          std::swap(lhs_, rhs_);
        }
      }
    }
  }

  static inline bool is_equality(const z3::expr& e) {
    if (!e.is_bool())
      return false;
    auto k = e.decl().decl_kind();
    return e.num_args() == 0 || k == Z3_OP_EQ || 
        (k == Z3_OP_NOT && e.arg(0).num_args() == 0);
  }

  //! returns true if the expression is an equality
  inline bool is_equality() const { return is_equality_; }
  inline z3::expr lhs() { return lhs_; }
  inline z3::expr rhs() { return rhs_; }

  inline std::pair<z3::expr, z3::expr> pair() {
    return std::make_pair(lhs_, rhs_);
  }

  inline void swap() {
    std::swap(lhs_, rhs_);
  }

 private:
  bool is_equality_ = false;
  z3::expr lhs_;
  z3::expr rhs_;
};
}

#endif
