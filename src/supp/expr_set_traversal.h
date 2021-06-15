// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef expr_traversal_hpp__
#define expr_traversal_hpp__


#include "checker_types.h"
#include "supp/expr_supp.h"
#include "supp/expr_iterators.h"

#include <unordered_set>

namespace euforia {
//*-------------------------------------------------------------------------------*
// given a collection of exprs to look for, finds if a given expr contains them
class ExprSetTraversal {
  ExprSet targets_;
  ExprSet matches_;
 public:
  void AddTarget(const z3::expr&);
  //! does not set matches_
  bool ExprContainsTarget(const z3::expr&);

  template <class T>
  ExprSetTraversal(T begin, T end) {
    AddTargets(begin, end);
  }

  template <class T>
  explicit ExprSetTraversal(const T& collection) {
    AddTargets(std::begin(collection), std::end(collection));
  }


  template <class T>
  void AddTargets(const T& collection) {
    AddTargets(std::begin(collection), std::end(collection));
  }
  
  template <class T>
  void AddTargets(T begin, T end) {
    auto I = begin;
    while (I != end) {
      AddTarget(*I++);
    }
  }

  inline const ExprSet& targets() const {
    return targets_;
  }

  inline void ResetMatches() {
    matches_.clear();
  }

  inline const ExprSet& matches() const { return matches_; }


  //! sets matches_
  void Traverse(const z3::expr&);

  template <typename T>
  void Traverse(T begin, T end) {
    for (auto it = begin; it != end; ++it) {
      Traverse(*it);
    }
  }
};


  
}

#endif
