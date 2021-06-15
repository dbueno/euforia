// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "xsys/var_info_traversal.h"

#include "supp/expr_iterators.h"
#include "xsys/transition_system.h"

namespace euforia {
//*-------------------------------------------------------------------------------*
// VarInfoTraversal
  
void VarInfoTraversal::Reset() {
  vars_used_.clear();
  vars_defd_.clear();
  inputs_used_.clear();
  constants_used_.clear();
}

void VarInfoTraversal::Traverse(const z3::expr& e_in) {
  for (auto I = po_expr_iterator::begin(e_in), E = po_expr_iterator::end(e_in);
       I != E; ++I) {
    auto e = *I;
    if (auto v = xsys_.FindVar(e)) {
      if (z3::eq(e, v->current())) {
        vars_used_.insert(e);
      } else {
        vars_defd_.insert(e);
      }
    } else if (xsys_.FindInput(e)) {
      inputs_used_.insert(e);
    } else if (IsUConstant(e)) {
      constants_used_.insert(e);
    }
  }
}

  

}
