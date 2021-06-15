// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "z3++.h"

#include <iostream>
#include <tuple>

using namespace z3;
using namespace std;


//*-------------------------------------------------------------------------------*
// for testing

void EquivCheck(z3::context& ctx, const z3::expr& f1, const z3::expr& f2) {
  cerr << "*** checking ***" << endl;
  cerr << "f1: " << f1 << endl;
  cerr << "is equivalent to" << endl;
  cerr << "f2: " << f2 << endl;
  z3::solver solver(ctx);
  solver.add(f1 != f2);
  auto result = solver.check();
  if (result == z3::sat) {
    cerr << "ERROR: equivalence check failed" << endl;
    cerr << "f1: " << f1 << endl;
    cerr << "NOT EQUIVALENT TO" << endl;
    cerr << "f2: " << f2 << endl;
    auto model = solver.get_model();
    cerr << endl << "model:" << endl;
    cerr << model << endl;

  }
  assert(result == z3::unsat);
}

void ValidityCheck(z3::context& ctx, const z3::expr& assumption, const z3::expr& consequent) {
  cerr << "*** checking validity ***" << endl;
  cerr << "a -> c: " << z3::implies(assumption, consequent) << endl;
  z3::solver solver(ctx);
  solver.add(assumption);
  solver.add(!consequent);
  auto result = solver.check();
  if (result == z3::sat) {
    cerr << "ERROR: validity check failed" << endl;
    cerr << "NOT VALID" << endl;
    auto model = solver.get_model();
    cerr << endl << "model for a & !c:" << endl;
    cerr << model << endl;

  }
  assert(result == z3::unsat);
}

//*-------------------------------------------------------------------------------*
//

static void array_demo() {
  context cxt;
  solver solver(cxt);

  auto A = cxt.constant("A", cxt.array_sort(cxt.bv_sort(32), cxt.bv_sort(8)));
  auto B = cxt.constant("B", cxt.array_sort(cxt.bv_sort(32), cxt.bv_sort(8)));

  auto i = cxt.constant("i", cxt.bv_sort(32)), j = cxt.constant("j", cxt.bv_sort(32));
  auto x = cxt.constant("x", cxt.bv_sort(8)), y = cxt.constant("y", cxt.bv_sort(8));

  auto A1 = store(A, i, x);
  auto A2 = store(A, j, y);

  solver.add(A == B);

  solver.check();
  auto model = solver.get_model();

  cerr << "model:" << endl;
  cerr << model << endl;

  cerr << "eval(A==B):" << endl;
  cerr << model.eval(A==B) << endl;
}




void NormalizeForVmt(z3::context& ctx, const z3::expr& e) {
  goal g(ctx);
  g.add(e);

  //describe_tactics();

  //tactic t(ctx, "tseitin-cnf");
  tactic t1(ctx, "simplify");
  tactic t2(ctx, "tseitin-cnf");
  tactic t = t1 & t2;
  apply_result r = t(g);
  cerr << r << endl;
}


int main(int, char **) {
  //array_demo();
  //
  //
  z3::context ctx;
  auto b = ctx.bool_const("b");
  auto c = ctx.bool_const("c");
  auto x = ctx.bv_const("x", 32);
  auto y = ctx.bv_const("y", 32);
  auto z = ctx.bv_const("z", 32);
  
#if 0
  EfficientIteRewrite rmite;

  cerr << (x == y) << endl;
  cerr << rmite.rewrite(x == y) << endl;

  auto i1 = z3::ite(c, x, y);
  auto i2 = z3::ite(c, y, x);
  auto f1 = (i1 == x);
  cerr << f1 << endl;
  auto rw1 = rmite.RemoveFormulaItes(f1);
  cerr << rw1 << endl;
  //ValidityCheck(ctx, f1, rw1);
  auto f2 = (z == x+ite(c,y,x));
  auto rw2 = rmite.RemoveFormulaItes(f2);
  cerr << f2 << endl;
  cerr << rw2 << endl;
  //EquivCheck(ctx, x+ite(c,y,x), rmite.rewrite(x + z3::ite(c, y, x)));

  //auto i7 = x + ite(ite(c, b, !b), y, x);
  //EquivCheck(ctx, i7, rmite.rewrite(i7));

  //NormalizeForVmt(ctx, (i1 == i2) && (y == x+ite(ite(c, b, !b), y, x)));
#endif
}
