// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include <utility>
#include <type_traits>

#include "supp/expr_visitor.h"

namespace euforia {

//! This class helps bottom-up rewriting of expressions. Most expressions e can
//! be rewritten in terms of new arguments (args) using the code:
//! \code
//! e.decl(args)
//! \endcode
//! But when the arguments changes type, sometimes this is unsafe. For
//! instance, the type of equality between bit vectors is different from the
//! type of equality between terms in Z3. In order to handle this properly,
//! this class will not use the decl() of the expression, but call the
//! constructor for that kind of node again.
//!
//! To use it, see make_identity_rewriter.
//!
//! This class is templated so that callers can choose to store a reference to
//! the arguments or allocate storage inline. This is handled by deduction with
//! make_identity_rewriter.
template <typename T>
class IdentityRewriter 
    : public ExprVisitor<IdentityRewriter<T>, z3::expr> {
 public:
  using Parent = ExprVisitor<IdentityRewriter<T>, z3::expr>;
  // This was shadowed for...reasons I don't remember from the standard.
  using Parent::visit;

  IdentityRewriter(std::add_rvalue_reference_t<T> args) 
      : args_(std::forward<T>(args)) {}
  
  //! Entry point for rewriter. Rewrites original expression e with new
  //! arguments given in constructor.
  //!
  //! \param e - expression to rewrite
  z3::expr operator()(const z3::expr& e) {
    assert(!e.is_app() || e.num_args() == args_.size());
    assert(!e.is_quantifier() || args_.size() == 1);
    assert(!e.is_var() || args_.empty());
    return Parent::visit(e);
  }

  z3::expr visitExpr(const z3::expr& e) {
    return e.decl()(args_);
  }

  z3::expr visitVAR(const z3::expr& e) {
    return e;
  }

  z3::expr visitQUANTIFIER(const z3::expr& e) {
    // This code just copies the quantifier variables into the new quantifier.
    // Another option is to scan the new body for variables and then use just
    // those. I hope I don't have to do that.
    auto& c = e.ctx();
    const unsigned n = Z3_get_quantifier_num_bound(c, e);
    std::vector<Z3_sort> sorts(n, c.bool_sort());
    std::vector<Z3_symbol> names(n, z3::symbol(c, Z3_mk_int_symbol(c, 0)));
    for (unsigned i = 0; i < n; i++) {
      sorts[i] = z3::sort(c, Z3_get_quantifier_bound_sort(c, e, i));
      names[i] = z3::symbol(c, Z3_get_quantifier_bound_name(c, e, i));
    }
    const unsigned weight = Z3_get_quantifier_weight(c, e);
    // XXX patterns are not supported
    return z3::expr(
        c,
        Z3_mk_quantifier(c, e.is_forall(), weight, 0, {}, n, sorts.data(),
                         names.data(), args_[0]));
  }

  z3::expr visitEQ(const z3::expr&) {
    return expr_eq(args_[0], args_[1]);
  }

  z3::expr visitITE(const z3::expr&) {
    return z3::ite(args_[0], args_[1], args_[2]);
  }

  z3::expr visitSELECT(const z3::expr&) {
    return z3::select(args_[0], args_[1]);
  }

 private:
  T args_;
};

//! Creates an IdentityRewriter using the given sequence of rewritten arguments
template <typename T>
auto make_identity_rewriter(T&& t) {
  return IdentityRewriter<T>(std::forward<T>(t));
}

} // end namespace euforia
