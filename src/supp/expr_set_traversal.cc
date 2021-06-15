// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/expr_set_traversal.h"
#include "supp/expr_iterators.h"

using namespace std;

namespace euforia {

//*----------------------------------------------------------------------------*
// ExprSetTraversal


void ExprSetTraversal::AddTarget(const z3::expr& e) {
  targets_.insert(e);
}

bool ExprSetTraversal::ExprContainsTarget(const z3::expr& e_in) {
  for (auto I = po_expr_iterator::begin(e_in), E = po_expr_iterator::end(e_in);
       I != E; ++I) {
    if (targets_.find(*I) != targets_.end()) {
      return true;
    }
  }
  return false;
}

void ExprSetTraversal::Traverse(const z3::expr& e_in) {
  for (auto it = po_expr_iterator::begin(e_in),
       ie = po_expr_iterator::end(e_in); it != ie; ++it) {
    if (targets_.find(*it) != targets_.end()) {
      matches_.insert(*it);
    }
  }
}

}
