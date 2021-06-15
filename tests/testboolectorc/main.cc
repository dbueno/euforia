// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

extern "C" {
#include "boolector.h"
}


int main(int, char**) {
  auto b = boolector_new();
  boolector_set_opt(b, BTOR_OPT_MODEL_GEN, 2);

  auto idxsort = boolector_bitvec_sort(b, 64);
  auto valsort = boolector_bitvec_sort(b, 64);
  auto arrsort = boolector_array_sort(b, idxsort, valsort);

  auto zero_val = boolector_zero(b, valsort);

  auto v1 = boolector_var(b, idxsort, "v1");
  auto i1 = boolector_var(b, idxsort, "i1");
  auto a1 = boolector_array(b, arrsort, "a1");
  auto a2 = boolector_array(b, arrsort, "a2");
  auto a2next = boolector_array(b, arrsort, "a2+");

  auto e32 = boolector_eq(b, a1, a2next);
  auto e37 = boolector_read(b, a1, v1);
  auto e38 = boolector_read(b, a2next, v1);
  auto e39 = boolector_eq(b, e37, e38);
  auto f53 = boolector_write(b, a2, i1, zero_val);
  auto e55 = boolector_eq(b, a1, f53);

  boolector_assert(b, boolector_not(
          b, boolector_and(b, boolector_not(b, e39), e32)));
  boolector_assert(b, e55);

  boolector_dump_smt2(b, stdout);

  return 0;
}

