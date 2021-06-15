// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/boolector_evaluator.h"

#include "xsys/vmt_transition_system.h"

using namespace llvm;

namespace euforia {

z3::expr BoolectorEvaluator::Eval(const z3::expr& e) {
  return Rewrite(e);
}
  
// Called by Rewrite
z3::expr BoolectorEvaluator::visitExpr(const z3::expr& e) {
  return solver_.get_model()->Eval(e);
}

}


