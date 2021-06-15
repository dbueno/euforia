// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "xsys/concrete_vmt_transition_system.h"

namespace euforia {
namespace vmt {

void
ConcreteVmtTransitionSystem::collect_static_statistics(Statistics *st) const {
  VmtTransitionSystem::collect_static_statistics(st);
}

} // end namespace vmt
} // end namespace euforia
