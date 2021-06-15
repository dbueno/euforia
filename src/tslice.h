// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef tslice_hpp
#define tslice_hpp

#include "supp/expr_supp.h"

namespace euforia {
  
/// Represents a cube s+ and the necessary slice of the transition relation
/// to feasibility check z & T & s+ without requering all of T
struct TSlice {
  // stuff related to the cube
  ExprSet target_constraints;// put these in the core
  // stuff related to the program's bare necessities
  ExprSet transition_constraints; // don't put these in the core
};

std::ostream& operator<<(std::ostream&, const TSlice&);
}
#endif
