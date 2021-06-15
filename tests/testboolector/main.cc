// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno


#include "supp/boolector_evaluator.h"
#include "supp/boolector_solver.h"

using namespace euforia;

// The question is: is it my rewriting or is it boolector?  Write a C boolector
// program with the same constraints and run it to see if its printing is not
// parseable.

int main(int, char **) {
  z3::context c;
  auto ctx = [&]() -> z3::context& { return c; };
  
  boolector::BoolectorSolver s(ctx());
  auto btor = s.btor_solver();

  auto idxsort = ctx().bv_sort(64);
  auto valsort = ctx().bv_sort(64);
  auto arrsort = ctx().array_sort(idxsort, valsort);

  auto zero_val = ctx().bv_val(0, valsort.bv_size());

  auto v1 = ctx().constant("v1", idxsort);
  auto i1 = ctx().constant("i1", idxsort);
  auto a1 = ctx().constant("a1", arrsort);
  auto a2 = ctx().constant("a2", arrsort);
  auto a2next = ctx().constant("a2+", arrsort);

  auto e32 = (a1 == a2next);
  auto e37 = a1[v1];
  auto e38 = a2next[v1];
  auto e39 = (e37 == e38);
  auto f53 = z3::store(a2, i1, zero_val);
  auto e55 = (a1 == f53);

  s.Add(!(!e39 && e32));
  s.Add(e55);

  btor->Print(std::cout);

  return 0;
}
