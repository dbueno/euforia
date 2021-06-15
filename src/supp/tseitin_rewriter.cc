// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/tseitin_rewriter.h"

#include <llvm/ADT/GraphTraits.h>

#include "supp/expr_iterators.h"
#include "supp/rewriter.h"

using namespace std;
using namespace euforia;
using namespace llvm;



namespace euforia {
class TseitinRewriter::Impl {
 public:
  FreshFunction fresh_var_;

  Impl(z3::context&, FreshFunction f) : fresh_var_(f) {}

  z3::expr FreshVar(const z3::expr&) {
    auto b = fresh_var_("tseitin");
    return b;
  }
};

TseitinRewriter::TseitinRewriter(z3::context& c, FreshFunction f) 
  : pimpl_(std::make_unique<Impl>(c, f)),
    defs_(std::make_unique<TseitinMap>()) {}

TseitinRewriter::~TseitinRewriter() = default;
  
void TseitinRewriter::operator()(const z3::expr& e) {
  // Rewrites each conjunct by introducing Tseitin variables.
  clauses_.push_back(Rewrite(e));
  // for (const z3::expr& c : ExprConjuncts(e)) {
  //   clauses_.push_back(Rewrite(c));
  // }
  logger.Log(4, "tseitin conversion introduced {} variables and produced {} clauses",
             defs_->size(), clauses_.size());
  for (auto& clause : clauses_) {
    logger.Log(4, "  {}", clause);
  }
  logger.Log(4, "{} tseitin definitions", defs_->size());
  for (auto& p : defs_->left) {
    auto& k = p.first;
    auto& v = p.second;
    logger.Log(4, "  {} = {}", k, v);
  }
}

void TseitinRewriter::Reset() {
  ExprRewriter::Reset();
  clauses_.clear();
  defs_ = std::make_unique<TseitinMap>();
}



z3::expr TseitinRewriter::visitExpr(const z3::expr& e) {
  return CreateClause(e, e.decl()(NewArgsExprVector(e)));
}

z3::expr TseitinRewriter::CreateClause(const z3::expr& e,
                                       const z3::expr& e_new_in) {
  auto e_new = e_new_in;
  if (!e.is_bool())
    return e_new;
  // Tries to not create tseitin things for one- hots
  // XXX test against top
  if (is_or(e_new) && e_new.num_args() == 2 &&
      (is_not(e_new.arg(0)) && e_new.arg(0).arg(0).num_args() == 0) &&
      (is_not(e_new.arg(1)) && e_new.arg(1).arg(0).num_args() == 0))
    return e_new;
  
  // Creates Tseitin var for Boolean logic nodes
  if (!IsLiteral(e_new) ||
      (!is_not(e_new) && !is_eq(e_new) && /*IsUninterp(e) &&*/
       e_new.num_args() > 0)) {
    auto b = pimpl_->FreshVar(e_new);
    defs_->insert({b, e_new});
    // e_new = b;
  }
  return e_new;
}

} // end namespace euforia
