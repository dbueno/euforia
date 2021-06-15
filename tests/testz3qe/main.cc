// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include <z3++.h>
#include <fmt/format.h>
#include <fmt/ostream.h>

#include <iostream>
#include <tuple>

using namespace z3;
using namespace std;


// Performs quantifier elimination on the given formula and displays what
// happened  afterward
int main(int argc, char **argv) {
  context c;
  auto ctx = [&]() -> z3::context& { return c; };

  if (argc < 2) {
    auto idx_sort = ctx().bv_sort(8);
    auto val_sort = ctx().bv_sort(32);
    auto array_sort = ctx().array_sort(idx_sort, val_sort);

    auto xv0 = ctx().constant("xv0", array_sort);
    auto x = ctx().constant("x", array_sort);
    auto x_next = ctx().constant("x+", array_sort);

    auto p1 = ctx().constant("p1", idx_sort);
    auto p2 = ctx().constant("p2", idx_sort);

    auto v1 = ctx().constant("v1", val_sort);
    auto v2 = ctx().constant("v2", val_sort);

    solver s(ctx());
    auto formula = select(xv0, p1) == v1;
    //formula = formula && x == xv0;
    // If this is store(x, p2, v2) instead then z3 comes back with an answer
    // instantly.
    formula = formula && x_next == store(xv0, p2, v2);

    expr_vector vars(ctx());
    vars.push_back(xv0);
    auto exist = exists(vars, formula);
    fmt::print("existential formula:\n{}\n\n", exist);
    auto qe = tactic(ctx(), "qe");
    goal g(ctx());
    g.add(exist);
    auto exist_elim = qe(g);
    fmt::print("turned into the following subgoals:\n");
    for (unsigned i = 0; i < exist_elim.size(); i++) {
      fmt::print("  subgoal {}: {}\n", i, exist_elim[i].as_expr());
    }
    return 0;
  }
  
  auto assertion = ctx().parse_file(argv[1]);
  goal g(ctx());
  g.add(assertion);

  fmt::print("goal: {}\n", g);

  auto simplifier = z3::tactic(ctx(), "qe") &
      z3::repeat(z3::tactic(ctx(), "ctx-simplify")) &
      z3::tactic(ctx(), "simplify");// & z3::tactic(ctx(), "smt");

  auto after_qe = simplifier(g);
  for (unsigned i = 0; i < after_qe.size(); i++) {
    fmt::print("  subgoal {}: {}\n", i, after_qe[i].as_expr());
  }
}
