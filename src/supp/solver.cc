// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/solver.h"

#include <fmt/format.h>
#include <fmt/ostream.h>

using namespace std;

namespace euforia {

std::ostream& operator<<(std::ostream& out, const CheckResult& r) {
  switch (r) {
    case CheckResult::kSat:
      fmt::print(out, "sat");
      break;

    case CheckResult::kUnsat:
      fmt::print(out, "unsat");
      break;

    case CheckResult::kUnknown:
      fmt::print(out, "unknown");
      break;
  }
  return out;
}

unique_ptr<Assignment> Model::assignment(z3::expr var) {
  return make_unique<Assignment>(var, Eval(var));
}

z3::expr Solver::TrackAssertion(const z3::expr& e, const char *prefix) {
  if (e.is_bool() && e.num_args() == 0)
    return e;
  z3::expr b = FreshBool(e.ctx(), prefix);
  z3::expr assertion = z3::implies(b, e);
//    LOGD(spdlog::get("euforia"), "adding tracking assertion: {}", assertion);
  Add(assertion);
  tracked_assertions_.insert({b, e});
  tracking_bools_.insert({e, b});
  return b;
}

bool Solver::IsTracked(const z3::expr& b) const {
  return (tracked_assertions_.find(b) != tracked_assertions_.end());
}

z3::expr Solver::GetTracked(const z3::expr& b) const {
  return tracked_assertions_.at(b);
}

z3::expr Solver::GetTracked(const z3::expr& b, const z3::expr& def) const {
  if (auto loc = tracked_assertions_.find(b); loc != tracked_assertions_.end()) {
    return loc->second;
  }
  return def;
}

void Solver::ClearTracked() {
  tracked_assertions_.clear();
  tracking_bools_.clear();
}
}
