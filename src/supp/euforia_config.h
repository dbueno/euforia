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
  int no_check; // to test whether explicit initialization trumps
  int verify_invariant;
  int dump_abstract_queries;
  int minimize_invariant ;
  bool running_stats;
  int use_tseitin;
  int no_abstract_arrays;
  int abstract_array_select_fresh;
  int use_layered_refinement_queries;
  int refinement_queries_without_t;
  int sort_cubes;
  int use_only_bmc_refinement;
  int use_one_shot_bmc_refinement;
  int use_osbmc_slicing;
  int check_for_redundant_lemmas;
  int creduce;
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

