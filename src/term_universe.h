// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_TERM_UNIVERSE_H_
#define EUFORIA_TERM_UNIVERSE_H_

#include <propagate_const.h>
#include <set>

#include "supp/expr_supp.h"

namespace euforia {

// Use this class to sensitize to new predicates
class TermUniverse {
 public:
  TermUniverse();
  ~TermUniverse();

  void RegisterExpr(const z3::expr& e);

  class Impl;
 private:
  friend class Impl;

  SortMap<ExprSet> vars_;
  FuncDeclMap<int> apps_; // funcs and predicates
  std::experimental::propagate_const<std::unique_ptr<Impl>> impl_;

  void Add(const z3::expr& e);
};

//^----------------------------------------------------------------------------^
//

// Attempt to balance conciseness & not generating too many instantiations
class ApplicationSet {
 public:
  ApplicationSet(z3::func_decl f) : f_(f) {}

  void Add(const z3::expr& app);

 private:
  std::vector<std::set<z3::ExprWrapper>> args_;
  z3::func_decl f_;
};

} // end namespace euforia

#endif
