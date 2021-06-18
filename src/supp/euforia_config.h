// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef euforia_config_hpp
#define euforia_config_hpp

#include <ostream>
#include <string>

namespace euforia {
namespace config {

enum SupportedSolver { kZ3 = 1, kBoolector };

SupportedSolver solver_from_string(const std::string& s);

std::ostream& operator<<(std::ostream& out, const SupportedSolver& s);

struct Config {
  bool no_check; // to test whether explicit initialization trumps
  bool verify_invariant;
  bool dump_abstract_queries;
  bool minimize_invariant ;
  bool running_stats;
  int use_tseitin;
  bool no_abstract_arrays;
  bool abstract_array_select_fresh;
  bool use_layered_refinement_queries;
  bool refinement_queries_without_t;
  bool sort_cubes;
  bool use_only_bmc_refinement;
  bool use_one_shot_bmc_refinement;
  bool use_osbmc_slicing;
  bool check_for_redundant_lemmas;
  bool creduce;
  SupportedSolver refinement_solver;
  std::string dump_file; // file to dump to
};

std::ostream& operator<<(std::ostream&, const Config& c);

} // end namespace config

extern config::Config euforia_config;

//! Returns log level for normal log when it is used to print running statse.
//! Returns 0 if the running_stats are set, otherwise returns the level given
int StatLog(int level);

} // end namespace euforia

#endif

