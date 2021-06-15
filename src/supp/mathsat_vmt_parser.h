// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include <mathsat.h>

namespace euforia {
namespace vmt {

struct MathsatVmtAst {
  msat_env env;
  msat_term *terms;
  char **annots;
  size_t n;

  MathsatVmtAst(msat_env e) : env(e) {}
};

MathsatVmtAst VmtParse(const std::string& filename, msat_env);
MathsatVmtAst VmtParseStr(const std::string& data, msat_env);

}
}

  


