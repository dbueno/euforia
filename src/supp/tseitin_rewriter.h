// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef SUPP_TSEITIN_REWRITER_H_
#define SUPP_TSEITIN_REWRITER_H_

#include <boost/bimap/multiset_of.hpp>
#include <boost/bimap/unordered_set_of.hpp>
#include <memory>
#include <propagate_const.h>
#include <vector>
#include <z3++.h>

#include "supp/expr_def_bimap.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_visitor.h"

namespace euforia {

using TseitinMap = boost::bimap<
    boost::bimaps::unordered_set_of<z3::ExprWrapper, z3::HashExpr,
                                    z3::EqualToExpr>,
    boost::bimaps::multiset_of<z3::ExprWrapper>>;

class TseitinRewriter : public ExprRewriter<TseitinRewriter>,
    public ExprVisitor<TseitinRewriter, z3::expr> {
 public:
  using FreshFunction = std::function<z3::expr(const char *)>;

  TseitinRewriter(z3::context&, FreshFunction fresh_var);
  ~TseitinRewriter();

  //! Rewrites the given formula into a flat form by using Tseitin variables.
  //! This creates an equisatisfiable formula which is available through
  //! clauses(). The Tseitin variable definitions are available from
  //! TakeDefs().
  void operator()(const z3::expr&);

  //! Clears the clauses and defs
  void Reset();

  inline const std::vector<z3::expr>& clauses() const { return clauses_; }
  inline const TseitinMap& defs() const { return *defs_; }
  //! Transfers defs ownership to caller
  inline std::unique_ptr<TseitinMap> TakeDefs() { return std::move(defs_); }

  // overrides
  z3::expr visitExpr(const z3::expr&);

 private:
  class Impl;
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;
  std::vector<z3::expr> clauses_;
  // tseitin definitions
  std::unique_ptr<TseitinMap> defs_;

  z3::expr Convert(const z3::expr& e);
  z3::expr CreateClause(const z3::expr& e_orig, const z3::expr& e_new);
};
}

#endif
