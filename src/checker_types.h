// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef checker_types_hpp
#define checker_types_hpp

#include <fmt/format.h>
#include <fmt/ostream.h>
#include <string>
#include <vector>
#include <z3++.h>

#include "supp/debug.h"
#include "supp/logger.h"
#include "supp/scoped_time_keeper.h"

#define EUFORIA_FATAL_EXIT_CODE 42

#define EUFORIA_FATAL(...) do { \
  fmt::print(std::cerr, "euforia: fatal error at {}:{}: {}\n", \
             __FILE__, __LINE__, __VA_ARGS__); \
  std::cout.flush(); \
  std::cerr.flush(); \
  exit(EUFORIA_FATAL_EXIT_CODE); \
} while (false);


//^----------------------------------------------------------------------------^
// utilitios


namespace euforia {

extern const std::string uninterpreted_bv_sort_name;
extern const std::string uninterpreted_array_sort_name;
extern std::string LOG_DIR;

} // end namespace euforia

// Functions to invoke from the debugger
void mylog(const z3::expr& e);
void mylog(const z3::params& p);
void mylog(const z3::sort& s);
void mylog(const std::vector<z3::expr>& e);
void mylog(const z3::expr_vector& v);
void mylog(const z3::func_decl& f);
void mylog(const z3::model& model);
void mylog(const z3::func_interp& FI);



#endif /* checker_types_hpp */
