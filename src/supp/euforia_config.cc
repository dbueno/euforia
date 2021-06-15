// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/euforia_config.h"

#include <fmt/format.h>
#include <fmt/ostream.h>
#include <map>

namespace euforia {

extern std::string LOG_DIR;

namespace config {

SupportedSolver solver_from_string(const std::string& s) {
  auto choices = std::map<std::string, config::SupportedSolver>(
      {{"z3", kZ3},
       {"boolector", kBoolector}});
  if (auto search = choices.find(s); search != choices.end()) {
    return search->second;
  }
  throw std::runtime_error("unsupported solver: " + s);
}

std::ostream& operator<<(std::ostream& out, const SupportedSolver& s) {
  switch (s) {
    case kZ3:
      out << "z3";
      break;
    case kBoolector:
      out << "boolector";
      break;
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, const Config& c) {
#define PRFIELD(field) \
  fmt::print(out, "config.{}: {}\n", #field, c.field)

  PRFIELD(no_check);
  PRFIELD(verify_invariant);
  PRFIELD(dump_abstract_queries);
  PRFIELD(minimize_invariant);
  PRFIELD(running_stats);
  PRFIELD(use_tseitin);
  PRFIELD(no_abstract_arrays);
  PRFIELD(abstract_array_select_fresh);
  PRFIELD(use_layered_refinement_queries);
  PRFIELD(refinement_queries_without_t);
  PRFIELD(sort_cubes);
  PRFIELD(use_only_bmc_refinement);
  PRFIELD(use_one_shot_bmc_refinement);
  PRFIELD(use_osbmc_slicing);
  PRFIELD(refinement_solver);
  PRFIELD(dump_file);
  PRFIELD(check_for_redundant_lemmas);
  PRFIELD(creduce);
  fmt::print(out, "LOG_DIR: {}\n", LOG_DIR);

#undef PRFIELD
  return out;
}

} // end namespace config

int StatLog(int level) {
  if (euforia_config.running_stats) {
    return 0;
  } else {
    return level;
  }
}

} // end namespace euforia
