// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/mathsat_vmt_parser.h"

#include <stdexcept>
#include <cstdio>
#include <string>

using namespace std;

namespace euforia {
namespace vmt {


MathsatVmtAst VmtParse(const std::string& filename, msat_env env) {
  MathsatVmtAst ast(env);
    
  auto file = fopen(filename.c_str(), "r");
  int err = msat_annotated_list_from_smtlib2_file(env, file, &ast.n,
                                                  &ast.terms, &ast.annots);

  if (err) {
    auto msg = msat_last_error_message(env);
    throw runtime_error("mathsat error parsing annotated smt2: " +
                        string(msg));
  }
  
  return ast;
}

MathsatVmtAst VmtParseStr(const std::string& data, msat_env env) {
  MathsatVmtAst ast(env);
    
  int err = msat_annotated_list_from_smtlib2(env, data.c_str(), &ast.n,
                                             &ast.terms, &ast.annots);

  if (err) {
    auto msg = msat_last_error_message(env);
    throw runtime_error("mathsat error parsing annotated smt2: " +
                        string(msg));
  }
  
  return ast;
}

}
}
