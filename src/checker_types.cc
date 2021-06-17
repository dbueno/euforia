// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "checker_types.h"
#include "supp/expr_supp.h"
#include "supp/fmt_supp.h"
#include "cube.h"



using namespace std;



namespace euforia {
  
std::string LOG_DIR = "";
NameLogger nlogger;
Logger logger;
const std::string uninterpreted_bv_sort_name = "UBV";
const std::string uninterpreted_array_sort_name = "UA";

void CreduceAssert(bool x) {
  if (!x)
    exit(69);
}


}

void mylog(const z3::params& p) { std::cerr << p << std::endl; }
void mylog(const z3::sort& s) { std::cerr << s << std::endl; }
void mylog(const z3::func_decl& f) { std::cerr << f << std::endl; }
void mylog(const z3::expr& e) { std::cerr << e.get_sort() << ":" << e << std::endl; }
void mylog(const vector<z3::expr>& e) { fmt::print(std::cerr, "{}\n", e); }
void mylog(const z3::expr_vector& v) { std::cerr << v << std::endl; }
void mylog(const euforia::Cube& c) { fmt::print(std::cerr, "{}\n", c); }
void mylog(const euforia::TimedCube& t) { fmt::print(std::cerr, "{}\n", t); }
void mylog(const z3::model& model) { std::cerr << model << endl; }
void mylog(const z3::func_interp& FI) {
  for (unsigned i = 0; i < FI.num_entries(); i++) {
    auto entry = FI.entry(i);
    std::cerr << "(";
    for (unsigned j = 0; j < entry.num_args(); j++) {
      auto arg = entry.arg(j);
      std::cerr << arg << (j+1 < entry.num_args() ? ", " : "");
    }
    std::cerr << ") => " << entry.value() << std::endl;
  }
  std::cerr << "(*) => " << FI.else_value() << endl;
}





