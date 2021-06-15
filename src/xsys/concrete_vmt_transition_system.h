// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef concrete_vmt_transition_system_h
#define concrete_vmt_transition_system_h

#include "xsys/vmt_transition_system.h"

namespace euforia {
namespace vmt {

class ConcreteVmtTransitionSystem : public VmtTransitionSystem {
 public:
  ConcreteVmtTransitionSystem(MathsatVmtAst& ast, z3::context& c)
      : VmtTransitionSystem(ast, c) {}

  void collect_static_statistics(Statistics *st) const;
};

} // end namespace vmt
} // end namespace euforia

#endif
