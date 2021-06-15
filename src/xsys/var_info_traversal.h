// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef vars_traversal_hpp
#define vars_traversal_hpp

#include <memory>

#include "supp/expr_supp.h"
#include "supp/expr_visitor.h"

namespace euforia {
  class TransitionSystem;
  
//*-------------------------------------------------------------------------------*
//VarInfoTraversal
//
class VarInfoTraversal {
 public:
  explicit VarInfoTraversal(const TransitionSystem& ts) : xsys_(ts) {}

  inline const ExprSet& vars_used() const { return vars_used_; }
  inline const ExprSet& vars_defd() const { return vars_defd_; }
  inline const ExprSet& inputs_used() const { return inputs_used_; }
  inline const ExprSet& constants_used() const { return constants_used_; }

  /// Clears all sets
  void Reset();

  /// Traverse expr, add any var input and constant information
  void Traverse(const z3::expr&);
  
  template <class T>
  void Traverse(T begin, T end) {
    for (auto it = begin; it != end; ++it) {
      Traverse(*it);
    }
  }

 private:
  const TransitionSystem& xsys_;
  ExprSet vars_used_;
  ExprSet vars_defd_;
  ExprSet inputs_used_;
  ExprSet constants_used_; // IsUConstant
};

  

}

#endif
