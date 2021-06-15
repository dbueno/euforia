#include <iostream>
#include <fstream>

#include "backend_supp.hpp"
#include "simple_transition_system.hpp"
#include "checker.hpp"
#include "counterexample.hpp"
#include "expr.hpp"


using namespace EUFORIA;



using namespace z3;
using namespace std;

namespace spd = spdlog;


void test1() {
  z3::context ctx;
  simple_transition_system ts(ctx);
  const int W = 2;
  const int MAX = 3; // 0xff on W bits
  const state_var& Xv = ts.addVar("X", ctx.bv_const("X", W), ctx.bv_const("X+", W));
  const state_var& Yv = ts.addVar("Y", ctx.bv_const("Y", W), ctx.bv_const("Y+", W));
  z3::expr X = Xv.zcurr;
  z3::expr Y = Yv.zcurr;
  
  // initially X and Y are 0
  //
  ts.I = (X==0 && Y==0);
  cerr << "I: " << ts.I << endl;
  
  // next states
  ts.addNextState(Xv, ite(z3::ugt(Y,X),
                           X,
                           ite(Y==X || X!=MAX, X+W, Y)));
  ts.addNextState(Yv, ite(Y==X,
                           Y+W,
                           ite(z3::ugt(Y,X) || X!=MAX, Y, X)));
  
  
  // property
  ts.P = (z3::ule(Y,X));
  cerr << "P: " << ts.P << endl;
  
  ts.prepare();
  checker chk(ts);
  bool hasCx = chk.run();
  assert(!hasCx);
  
  if (hasCx) {
    cerr << "Property does NOT hold." << endl;
    chk.computeCounterexample()->print(cout);
  } else {
    cerr << "Property holds!" << endl;
  }
}

void test2() {
  z3::context ctx;
  simple_transition_system ts(ctx);
  const int W = 2;
  const int MAX = 3; // 0xff on W bits
  const state_var& Xv = ts.addVar("X", ctx.bv_const("X", W), ctx.bv_const("X+", W));
  const state_var& Yv = ts.addVar("Y", ctx.bv_const("Y", W), ctx.bv_const("Y+", W));
  z3::expr X = Xv.zcurr;
  z3::expr Y = Yv.zcurr;
  
  // initially X and Y are 0
  //
  ts.I = (X==0 && Y==0);
  cerr << "I: " << ts.I << endl;
  
  // next states
  ts.addNextState(Xv, ite(z3::ule(X,Y),
                          X+1,
                          ctx.bv_val(0, W)));
  ts.addNextState(Yv, ite(Y==0,
                          ctx.bv_val(MAX, W),
                          ite(z3::ugt(Y,X), Y, ctx.bv_val(0, W))));
  
  
  // property
  ts.P = (z3::ule(X,Y));
  cerr << "P: " << ts.P << endl;
  
  ts.prepare();
  checker chk(ts);
  bool hasCx = chk.run();
  assert(!hasCx);
  
  if (hasCx) {
    cerr << "Property does NOT hold." << endl;
    chk.computeCounterexample()->print(cout);
  } else {
    cerr << "Property holds!" << endl;
  }
}

void test3() {
  z3::context ctx;
  simple_transition_system ts(ctx);
  const int W = 2;
  const int MAX = 3; // 0xff on W bits
  const state_var& Xv = ts.addVar("X", ctx.bv_const("X", W), ctx.bv_const("X+", W));
  const state_var& Yv = ts.addVar("Y", ctx.bv_const("Y", W), ctx.bv_const("Y+", W));
  z3::expr X = Xv.zcurr;
  z3::expr Y = Yv.zcurr;
  
  // initially X and Y are 0
  //
  ts.I = (X==0 && Y==0);
  cerr << "I: " << ts.I << endl;
  
  // next states
  ts.addNextState(Xv, ite(z3::ult(X,Y),
                          X+1,
                          ctx.bv_val(MAX, W)));
  ts.addNextState(Yv, ite(Y==0,
                          ctx.bv_val(MAX, W),
                          ite(z3::ugt(Y,X), Y, ctx.bv_val(0, W))));
  
  
  // property
  ts.P = (z3::ule(X,Y));
  cerr << "P: " << ts.P << endl;
  
  ts.prepare();
  checker chk(ts);
  bool hasCx = chk.run();
  assert(hasCx);
  
  if (hasCx) {
    cerr << "Property does NOT hold." << endl;
    auto cx = chk.computeCounterexample();
    cx->print(cout);
  } else {
    cerr << "Property holds!" << endl;
  }
}

void test_cube() {
  z3::context ctx;
  simple_transition_system TS(ctx);
  const state_var& a = TS.addVar("a", ctx.bool_const("a"), ctx.bool_const("a+"));
  const state_var& b = TS.addVar("b", ctx.bool_const("b"), ctx.bool_const("b+"));
  const state_var& c = TS.addVar("c", ctx.bool_const("c"), ctx.bool_const("c+"));
  TS.prepare();
  
  cube cu;
  
  auto lit1 = a.zcurr == b.zcurr;
  auto lit2 = a.znext != b.zcurr;
  cu.push(lit1, TS.substNext(lit1));
  assert(cu.size() == 1);
  assert(cu.contains(lit1));
  assert(!cu.contains(lit2));
  
  
  for (auto& lit : cu) {
    assert(z3::eq(lit, lit1));
  }
  
  {
    // try erase
    cube c2;
    c2.push(a.zcurr, TS.substNext(a.zcurr));
    c2.push(b.zcurr, TS.substNext(b.zcurr));
    c2.push(c.zcurr, TS.substNext(c.zcurr));
    assert(c2.size() == 3);
    auto c2_it = c2.begin();
    while (c2_it != c2.end()) {
      auto lit = *c2_it;
      if (z3::eq(lit, b.zcurr)) {
        c2_it = c2_it.erase();
      } else {
        ++c2_it;
      }
    }
    assert(c2.size() == 2);
    assert(c2.contains(a.zcurr));
    assert(c2.contains(c.zcurr));
    assert(!c2.contains(b.zcurr));
  }

  {
    // try replace
    cube c2;
    c2.push(a.zcurr, TS.substNext(a.zcurr));
    c2.push(b.zcurr, TS.substNext(b.zcurr));
    c2.push(c.zcurr, TS.substNext(c.zcurr));
    assert(c2.size() == 3);
    auto c2_it = c2.begin();
    while (c2_it != c2.end()) {
      auto lit = *c2_it;
      if (z3::eq(lit, b.zcurr)) {
        // straight replace, unsafe in general
        c2_it.replace(b.zcurr != a.zcurr, TS.substNext(b.zcurr != a.zcurr));
      }
      ++c2_it;
    }
    assert(c2.size() == 3);
    assert(c2.contains(a.zcurr));
    assert(c2.contains(c.zcurr));
    assert(c2.contains(b.zcurr != a.zcurr));
    assert(!c2.contains(b.zcurr));
  }

}

void test_uninterpreted_partition() {
  // figure out how to used uninterpreted functions
  z3::context ctx;
  auto termSort = ctx.uninterpreted_sort(TERM_SORT_NAME);
  auto x = ctx.constant("x", termSort);
  auto y = ctx.constant("y", termSort);
  auto z = ctx.constant("z", termSort);
  
  solver s(ctx);
  s.add(x == y);
  s.add(y != z);
  auto result = s.check();
  if (result == z3::sat) {
    auto model = s.get_model();
    auto rx = model.eval(x), ry = model.eval(y), rz = model.eval(z);
    cerr << "x: " << rx << endl;
    cerr << "y: " << ry << endl;
    cerr << "z: " << rz << endl;
    expr_umap<z3::expr> rep;
    rep.insert({rx, x});
    rep.insert({ry, y});
    assert(rep.find(model.eval(x)) != rep.end());
    assert(rep.find(model.eval(y)) != rep.end());
    assert(rep.find(model.eval(z)) == rep.end());

    vector<z3::expr> COI({x, y});
    uninterpreted_partition UP(model, begin(COI), end(COI));
    UP.insert(z);
    assert(UP.same(x, y));
    assert(!UP.same(y, z));
    assert(!UP.same(x, z));
    assert(z3::eq(UP.find(x), x) || z3::eq(UP.find(y), y));
    assert(z3::eq(UP.find(z), z));
    cerr << "find(x): " << UP.find(x) << endl;
    cerr << "find(y): " << UP.find(y) << endl;
    cerr << "find(z): " << UP.find(z) << endl;
    UP.print(cerr);
    cerr << UP.formula() << endl;
  }
  
}

void test_z3_models() {
  z3::context ctx;
  z3::solver S(ctx);
  
  auto x = ctx.bool_const("x");
  auto y = ctx.bool_const("y");
  
  S.push();
  S.add(x == y);
  auto result = S.check();
  assert(result == z3::sat);
  z3::model m1 = S.get_model();
  
  S.pop();
  S.push();
  
  S.add(x == !m1.eval(x));
  S.add(x == y);
  result = S.check();
  assert(result == z3::sat);
  z3::model m2 = S.get_model();
  
  assert(!z3::eq(m1.eval(x), m2.eval(x)));
  assert(!z3::eq(m1.eval(x), m2.eval(y)));
}


#include "boolector_supp.hpp"
using namespace boolector;

void test_boolector() {
  boolector::btor B;
  auto entryShell = B.var(1, "@L-entry-$shell");
  auto notEntryShell = !entryShell;
  
  unordered_map<int, boolector::boolector_node> M;
  
  boolector::boolector_node entryShellCopy = entryShell;
  auto entryShellCopy2(entryShell);
//  mylog(entryShellCopy);
  auto theAnd = entryShellCopy && notEntryShell;
  
  M.insert({1, entryShell});
  M.insert({2, notEntryShell});
  M.insert({3, theAnd});
  
  assert(M.at(1) == entryShellCopy);
  assert(M.at(1) == entryShellCopy2);
  assert(M.at(2) == notEntryShell);
  assert(M.at(3) == theAnd);
  
  unordered_map<boolector::boolector_node, int> M2;
  M2.insert({entryShell, 1});
  M2.insert({notEntryShell, 2});
  M2.insert({entryShellCopy, 3}); // should be ignored
  
  assert(entryShell.ID() == notEntryShell.ID()); // apparently (??!)
  assert(M2.at(entryShell) == 1);
  assert(M2.at(notEntryShell) == 2);

//  mylog(M.at(1));
//  mylog(M.at(2));
}

void test_boolector_failed_assumptions() {
  btor B;
  B.setOption(BTOR_OPT_INCREMENTAL, 1);
  // not sure why this is already set....
  B.setOption(BTOR_OPT_CHK_FAILED_ASSUMPTIONS, 0);

  auto x = B.var(8, "x"), y = B.var(8, "y"), z = B.var(8, "z");
  
  B.add(y.eq(z));
  B.add(x > y);
  B.add(y > B.cint(0, 8));
  B.add((x + y).eq(B.cint(0, 8)));
  
  auto result = B.check();
  switch (result) {
    case btor::result::SAT:
      assert(false);
      break;
      
    case btor::result::UNSAT:
      break;
  }
}



static string smt2Sort(const z3::sort& s) {
  if (s.is_bool()) {
    return "Bool";
  } else if (s.is_bv()) {
    return "(_ BitVec " + to_string(s.bv_size()) + ")";
  } else {
    FATAL("bad sort");
  }
}
static void checkRewrite(const z3::expr& z3Node) {
  btor bchk;
  Z3_to_boolector_node_rewriter R(bchk);
  auto btorNode = R.rewrite(z3Node);
  auto bprop = bchk.var(btorNode.width(), "$bprop");
  auto beq = (bprop.eq(btorNode));
  bchk.add(beq);
  
  auto zprop = z3Node.ctx().constant("$zprop", z3Node.get_sort());
  auto zeq = (zprop == z3Node);
  
  // Write both constraints to an SMT2 file and check it
  assert(!LOG_DIR.empty());
  string filename(LOG_DIR+"/check-conc.smt2");
  std::ofstream of(filename, std::ios::out);
  bchk.print(of);
  of << "(declare-fun $zprop () " << smt2Sort(zprop.get_sort()) << ")" << endl;
  of << "(assert " << zeq << ")" << endl;
  of << "(assert (not (= $bprop $zprop)))" << endl;
  of << "(check-sat)" << endl;
  of.close();
  
  //BREAK_INTO_DEBUGGER;
  // if sat,
  // add (set-option :produce-models true) to top of file
  // and (get-model) to bottom and rerun with boolector
  btor B;
  assert(btor::result::UNSAT == B.checkSMT2(filename));
}

void test_Z3_to_boolector_rewriter() {
  z3::context C;
  auto a = C.bool_const("a"), b = C.bool_const("b");
  auto x = C.bv_const("x", 8), y = C.bv_const("y", 8), z = C.bv_const("z", 8);
  auto M = C.constant("M", C.array_sort(C.bv_sort(8), C.bv_sort(8)));
  auto N = C.constant("N", C.array_sort(C.bv_sort(8), C.bv_sort(8)));
  z3::expr_vector xyz(C);
  xyz.push_back(x), xyz.push_back(y), xyz.push_back(z);
  
  checkRewrite(C.bool_val(true));
  checkRewrite(C.bool_val(false));
  checkRewrite(C.bv_val(4, 8));
  
  checkRewrite(z3::implies(a, b));
  checkRewrite(z3::ite(a, x, y));
  checkRewrite(x == y);
  checkRewrite(a == b);
  checkRewrite(!a);
  checkRewrite(a && b);
  checkRewrite(a && !b);
  checkRewrite(a || b);
  checkRewrite(a || !b);
  checkRewrite(z3::distinct(xyz));
  checkRewrite(x != y);
  checkRewrite(x < y);
  checkRewrite(x <= y);
  checkRewrite(z3::ule(x, y));
  checkRewrite(z3::ult(x, y));
  checkRewrite(x > y);
  checkRewrite(x >= y);
  checkRewrite(z3::uge(x, y));
  checkRewrite(z3::ugt(x, y));
  checkRewrite(x + y);
  checkRewrite(x + y + z);
  checkRewrite(x - y);
  checkRewrite(x - y - z);
  checkRewrite(x * y);
  checkRewrite(x * y * z);
  checkRewrite(x / y);
  checkRewrite(z3::udiv(x, y));
  checkRewrite(expr_shl(x, x.ctx().bv_val(4, 8)));
  checkRewrite(expr_ashr(x, x.ctx().bv_val(4, 8)));
  checkRewrite(expr_lshr(x, x.ctx().bv_val(4, 8)));
  checkRewrite(z3::concat(x, y));
  checkRewrite(x.extract(4,0));
  checkRewrite(x.extract(7,1));
  checkRewrite(x.extract(6,6));
  checkRewrite(x & y);
  checkRewrite(x | y);
  checkRewrite(x ^ y);
  checkRewrite(z3::bvsmod(x, y));
  checkRewrite(x % y);
//  checkRewrite(z3::bvsrem(x, y));
  // Can't test arrays because boolector uses UFs
//  checkRewrite(M == z3::store(N, x, y));
}


void test_z3_printer() {
  z3_expr_printer P;
  z3::context C;
  
  auto x = C.bv_const("x", 8), y = C.bv_const("y", 8);
  auto a = C.bv_const("a", 8), b = C.bv_const("b", 8);
  
  P.print((a+b) < (a+b));
  cerr << endl;
}


void test_expr() {
  EUFORIA::context c;
  
  auto foo = c.mkBVInput("foo", 32);
  assert(foo.hasInput);
}



int main(int argc, const char* argv[]) {
//  LOG_DIR = "/tmp";
  
  //Create console, multithreaded logger
  auto console = spd::stdout_logger_mt("console");
  //Formatting examples
  //console->info("Easy padding in numbers like {:08d}", 12);
  //console->info("Support for int: {0:d};  hex: {0:x};  oct: {0:o}; bin: {0:b}", 42);
  //console->info("Support for floats {:03.2f}", 1.23456);
  //console->info("Positional args are {1} {0}..", "too", "supported");
  
  //console->info("{:<30}", "left aligned");
  //console->info("{:>30}", "right aligned");
  //console->info("{:^30}", "centered");
  
  initializeLoggers(false);
  
  spdlog::get("pdr")->set_level(spdlog::level::level_enum::debug);
  
//  test1();
//  test2();
//  test3();
  test_cube();
  test_uninterpreted_partition();
  
  test_boolector();
  test_boolector_failed_assumptions();
  test_Z3_to_boolector_rewriter();
  
  test_z3_models();
  test_z3_printer();
  

  
  return 0;
}
