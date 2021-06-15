// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef cyclic_traversal_hpp
#define cyclic_traversal_hpp

#include "supp/expr_supp.h"

namespace euforia {
class CyclicTraversal {
  ExprSet do_not_expand_;
 protected:
  void ResetTraversal();
  bool Push(const z3::expr& e);
  void Pop(const z3::expr& e);

  CyclicTraversal() {}
};

}

#endif
