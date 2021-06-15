// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno


#include "tslice.h"

#include <fmt/format.h>
#include <fmt/ostream.h>

#include <numeric>

using namespace std;

namespace euforia {
std::ostream& operator<<(std::ostream& os, const TSlice& slice) {
  os << "tslice:" << endl;

  fmt::print(os, "  {} transition_constraints: ", slice.transition_constraints.size());
  if (!slice.transition_constraints.empty()) {
    os << accumulate(next(slice.transition_constraints.begin()), slice.transition_constraints.end(),
                     *slice.transition_constraints.begin(), expr_and);
    os << endl;
  }
  fmt::print(os, "  {} target_constraints:  ", slice.target_constraints.size());
  if (!slice.target_constraints.empty()) {
    os << accumulate(next(slice.target_constraints.begin()), slice.target_constraints.end(),
                     *slice.target_constraints.begin(), expr_and);
    os << endl;
  }
  return os;
}
}
