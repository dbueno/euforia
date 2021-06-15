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

context c;
static z3::context& ctx() {
  return c;
}

int problem1() {
  auto idx_sort = ctx().uninterpreted_sort("idx_sort");
  auto val_sort = ctx().uninterpreted_sort("val_sort");
  auto array_sort = ctx().array_sort(idx_sort, val_sort);
  auto xp = ctx().constant("xp", array_sort);
  auto x_next = ctx().constant("xp+", array_sort);
  auto zero_idx = ctx().constant("i", idx_sort);
  auto j_idx = ctx().constant("j", idx_sort);
  auto zero_val = ctx().constant("zero", val_sort);

  auto p = ctx().function("p", val_sort, ctx().bool_sort());

  params par(ctx());
  par.set("auto_config", false);
  solver s(ctx(), "QF_AUFBV");
  s.set(par);
  auto target_constraint = x_next != store(xp, zero_idx, zero_val);
  s.add(p(select(xp, zero_idx)) ||
        target_constraint);
  s.add(!p(select(xp, j_idx)));
  s.add(zero_idx == j_idx);
  fmt::print("assertions: {}\n", s.assertions());
  fmt::print("target_constraint: {}\n", target_constraint);

  auto result = s.check();
  cout << result << endl;
  if (result == check_result::sat) {
    auto m = s.get_model();
    fmt::print("model: {}\n", m);
    fmt::print("eval target_constraint: {}\n", m.eval(target_constraint));
  }
  return 0;
}


int main(int, char **) {
  auto idx_sort = ctx().uninterpreted_sort("IdxSort");
  auto val_sort = ctx().uninterpreted_sort("ValSort");
  auto i1 = ctx().constant("i1", idx_sort);
  auto i2 = ctx().constant("i2", idx_sort);
  auto v1 = ctx().constant("v1", val_sort);
  auto v2 = ctx().constant("v2", val_sort);
  auto xp = ctx().constant("xp", ctx().array_sort(idx_sort, val_sort));
  auto x  = ctx().constant("x", ctx().array_sort(idx_sort, val_sort));
  auto c1 = ctx().bool_val("c1");
  auto c2 = ctx().bool_val("c2");
  auto f  = ctx().function("f", val_sort, val_sort);
  solver s(ctx(), "QF_AUFBV");
  s.add(i1 != i2);
  s.add(v1 != v2);
  s.add(c1);
  s.add(xp == ite(c1, store(x, i1, v1), ite(c2, store(x, i1, f(select(x, i1))), x)));
  s.check();
  auto m = s.get_model();
  cout << m << endl;

  cout << m.eval(xp == store(x, i1, v1)) << endl;

  return 0;
}
