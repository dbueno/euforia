// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/expr_substitution.h"

#include <fmt/format.h>
#include <fmt/ostream.h>

namespace euforia {

ExprSubstitution::ExprSubstitution(const ExprSubstitution& other) 
    : src_(other.src_.ctx()), dst_(other.dst_.ctx()) {
  // z3::expr_vector's copy constructor SHARES POINTERS WITH THE SOURCE
  // INSTANCE.  so we need to manually copy the entries from other into our
  // src_ and dst_
  AddSubstitution(other.src_, other.dst_);
}

ExprSubstitution& ExprSubstitution::operator=(const ExprSubstitution& other) {
  src_ = z3::expr_vector(other.src_.ctx());
  dst_ = z3::expr_vector(other.dst_.ctx());
  // z3::expr_vector's copy constructor SHARES POINTERS WITH THE SOURCE
  // INSTANCE.  so we need to manually copy the entries from other into our
  // src_ and dst_
  AddSubstitution(other.src_, other.dst_);
  return *this;
}

z3::context& ExprSubstitution::ctx() {
  return src_.ctx();
}

void ExprSubstitution::Clear() {
  src_ = z3::expr_vector(ctx());
  dst_ = z3::expr_vector(ctx());
}

void ExprSubstitution::AddSubstitution(const z3::expr& eold,
                                       const z3::expr& enew) {
  assert(z3::eq(eold.get_sort(), enew.get_sort()));
  src_.push_back(eold); 
  dst_.push_back(enew);
}

z3::expr ExprSubstitution::operator()(const z3::expr& e) const {
  auto ret = e;
  return ret.substitute(src_, dst_);
  //return rewrite(e);
}

// parallel composition
ExprSubstitution
ExprSubstitution::operator&(const ExprSubstitution& other) const {
  ExprSubstitution ret(*this);
  ret.AddSubstitution(other.src_, other.dst_);
  return ret;
}

// overrides

//inline z3::expr visitExpr(const z3::expr& e) {
  //auto ret = e;
  //return ret.substitute(src_, dst_);
//}
//
void ExprSubstitution::Print(std::ostream& out) const {
  fmt::print("ExprSubstitution:\n");
  assert(src_.size() == dst_.size());
  for (unsigned i = 0; i < src_.size(); i++) {
    auto src_elt = src_[i];
    auto dst_elt = dst_[i];
    fmt::print(out, "    {} -> {}\n", src_elt, dst_elt);
  }
}

std::ostream& operator<<(std::ostream& os, const ExprSubstitution& s) {
  s.Print(os);
  return os;
}

//^----------------------------------------------------------------------------^


void CachingExprSubstitution::Clear() {
  src_ = z3::expr_vector(ctx());
  dst_ = z3::expr_vector(ctx());
}

void CachingExprSubstitution::AddSubstitution(const z3::expr& eold,
                                              const z3::expr& enew) {
  src_.push_back(eold);
  dst_.push_back(enew);
}

z3::expr CachingExprSubstitution::operator()(const z3::expr& e) {
  return Rewrite(e);
}

z3::expr CachingExprSubstitution::visitExpr(const z3::expr& e) {
  return e.decl()(NewArgsExprVector(e));
}

z3::expr CachingExprSubstitution::visitUNINTERPRETED(const z3::expr& e) {
  auto e_out = e;
  return e_out.substitute(src_, dst_);
}

}
