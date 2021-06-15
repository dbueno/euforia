// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "term_universe.h"

#include "supp/debug.h"
#include "supp/expr_iterators.h"
#include "supp/expr_visitor.h"

using namespace euforia;
using namespace std;

namespace {

class Walk : public ExprVisitor<Walk> {
 public:
  Walk(TermUniverse *u) : universe_(u) {}

  void operator()(const z3::expr& e) {
    for (const auto& d : ExprDescendents(e)) {
      visit(d);
    }
  }

  void visitExpr(const z3::expr& e) {
    if (e.is_app()) {
      _unused(universe_);
    }
  }

 private:
  TermUniverse *universe_;
};

} // end namespace euforia

//^----------------------------------------------------------------------------^
//

namespace euforia {

class TermUniverse::Impl {
 public:
  Impl(TermUniverse *u) : walk_(make_unique<Walk>(u)) {}

  unique_ptr<Walk> walk_;
};

TermUniverse::TermUniverse() : impl_(make_unique<Impl>(this)) {}

TermUniverse::~TermUniverse() = default;

void TermUniverse::RegisterExpr(const z3::expr& e) {
  (*impl_->walk_)(e);
}

void TermUniverse::Add(const z3::expr& app) {
  auto f = app.decl();
  apps_[f]++;
  for (const auto& arg : ExprArgs(app)) {
    vars_[arg.get_sort()].insert(arg);
  }
}

//^----------------------------------------------------------------------------^
//

void ApplicationSet::Add(const z3::expr& app) {
  assert(app.is_app());
  assert(z3::eq(f_, app.decl()));
  auto out = args_.begin();
  for (auto&& arg : ExprArgs(app)) {
    out++->insert(arg);
  }
}

} // end namespace euforia
