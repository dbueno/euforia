// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno


#include "xsys/cyclic_traversal.h"


namespace euforia {
//*-------------------------------------------------------------------------------*
//CyclicTraversal

void CyclicTraversal::ResetTraversal() {
  do_not_expand_.clear();
}

bool CyclicTraversal::Push(const z3::expr& e) {
  auto inserted = do_not_expand_.insert(e).second;
  return inserted;
}

void CyclicTraversal::Pop(const z3::expr& e) {
  do_not_expand_.erase(e);
}

}

