// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/expr_flattener.h"

#include <algorithm>

#include "supp/expr_iterators.h"

using namespace std;

namespace euforia {
z3::expr ExprFlattener::operator()(const z3::expr& e) {
  visited_.clear();
  flat_args_.clear();
  q_.clear();

  // Finds each AND/OR node and creates a list of its flattened arguments in
  // flat_args_.
  q_.push_back(e);
  while (!q_.empty()) {
    auto n = q_.back();
    q_.pop_back();
    if (!visited_.insert(n).second)
      continue;
    if (is_or(n)) {
      auto is_new = flat_args_.emplace(n, z3::expr_vector(e.ctx())).second;
      if (!is_new)
        continue;
      for (const z3::expr& c : ExprDisjuncts(n)) {
        flat_args_.at(n).push_back(c);
        q_.push_back(c);
      }
    } else if (is_and(n)) {
      auto is_new = flat_args_.emplace(n, z3::expr_vector(e.ctx())).second;
      if (!is_new)
        continue;
      for (const z3::expr& c : ExprConjuncts(n)) {
        flat_args_.at(n).push_back(c);
        q_.push_back(c);
      }
    } else {
      for (const z3::expr& k : ExprArgs(n)) {
        q_.push_back(k);
      }
    }
  }

  // logger.Log(1, "found {} flatteneds", flat_args_.size());
  // for (auto& [k, v] : flat_args_) {
  //   if (v.size() > 2) {
  //     logger.Log(1, "{} {} -> {}", k.decl().name(), v.size(), v);
  //   }
  // }

  // Using flat_args_, rewrite e so that all ANDs and ORs are flattened.
  auto ret = Rewrite(e);

  // Print some counst
  // for (auto it = df_expr_iterator::begin(ret),
  //      ie = df_expr_iterator::end(ret); it != ie; ++it) {
  //   if ((*it).num_args() <= 2)
  //     continue;
  //   if (is_and(*it)) {
  //     logger.Log(1, "and {}", (*it).num_args());
  //   }
  //   if (is_or(*it)) {
  //     logger.Log(1, "or {}", (*it).num_args());
  //   }
  // }
  return ret;
}

z3::expr ExprFlattener::visitExpr(const z3::expr& e) {
  return e.decl()(NewArgsExprVector(e));
}

z3::expr ExprFlattener::visitAND(const z3::expr& e) {
  if (auto search = flat_args_.find(e); search == flat_args_.end()) {
    // In this case, the AND is some sub-AND of another AND so we really
    // want to skip it.
    return e;
  } else {
    z3::expr_vector args(e.ctx());
    transform(begin(search->second), end(search->second),
              ExprVectorInserter(args),
              [&](const z3::expr& n) { return lookup(n); });
    return expr_mk_and(args);
  }
}

z3::expr ExprFlattener::visitOR(const z3::expr& e) {
  if (auto search = flat_args_.find(e); search == flat_args_.end()) {
    // In this case, the OR is some sub-OR of another AND so we really
    // want to skip it.
    return e;
  } else {
    z3::expr_vector args(e.ctx());
    transform(begin(search->second), end(search->second),
              ExprVectorInserter(args),
              [&](const z3::expr& n) { return lookup(n); });
    return expr_mk_or(args);
  }
}

} // end namespace euforia
