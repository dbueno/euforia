// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "checker_types.h"
#include "supp/std_supp.h"
#include "supp/marco.h"

using namespace std;
using namespace euforia;
using namespace euforia::marco;

int main() {
  z3::context ctx;
  auto x = ctx.real_const("x");
  auto y = ctx.real_const("y");

  std::vector<z3::expr> constraints;

  constraints.push_back(x>2);
  constraints.push_back(x<1);
  constraints.push_back(x<0);
  constraints.push_back((x+y>0) || (y<0));
  constraints.push_back((y>=0) || (x>= 0));
  constraints.push_back((y<0) || (x<0));
  constraints.push_back((y>0) || (x<0));

  Z3Solver s(ctx);
  MarcoEnumerator enumerate(s, constraints);
  logger.set_level(1);

  size_t i = 0;
  for (const auto& ms : enumerate) {
    fmt::print("{} [", ms.kind());
    boost::copy(ms, make_ostream_joiner(std::cout, ", "));
    fmt::print("]\n");
    if (++i == 10) {
      EUFORIA_FATAL("error in marco: too many subsets");
    }
  }
  if (i != 6) {
    EUFORIA_FATAL("expected 6 subsets, found {}}", i);
  } else {
    fmt::print("all tests passed\n");
  }

}
