// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include <algorithm>

#include "one_hot.h"

using namespace euforia;
using namespace std;

int main(int argc, char **argv) {
  z3::context ctx;
  OneHotConstraints ohc(ctx);

  int num_bools = 10;
  
  if (argc > 1)
    num_bools = std::stoi(argv[1]);

  for (int i = 0; i < num_bools; i++) {
    ohc.Insert(ctx.bool_const(("b" + to_string(i)).c_str()));
  }

  z3::solver s(ctx, "QF_AUFBV");
  s.add(ohc.at_most(OneHotConstraints::Config(3)));
  z3::expr at_least(ctx);
  ExprOrInserter out(at_least);
  std::copy(ohc.getBools().begin(), ohc.getBools().end(), out);
  s.add(out.get());

  vector<z3::expr> bools(ohc.getBools().begin(), ohc.getBools().end());
  for (auto it1 = bools.begin(), ie = bools.end(); it1 != ie; ++it1) {
    for (auto it2 = next(it1); it2 != ie; ++it2) {
      auto b1 = *it1;
      auto b2 = *it2;
      s.push();
      s.add(b1);
      s.add(b2);
      fmt::print("solving...\n");
      // Solve the constraints
      if (z3::check_result result = s.check();
          result == z3::check_result::sat) {
        auto model = s.get_model();
        fmt::print("sat\n");
        fmt::print("{}\n", s.assertions());
        fmt::print("{} & {}\n", b1, b2);
        for (auto& b : bools) {
          fmt::print("{}: {}\n", b, model.eval(b));
        }
        assert(false);
      } else {
        fmt::print("unsat\n");
      }
      s.pop();
    }
  }

  return 0;
}

