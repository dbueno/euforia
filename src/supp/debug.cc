// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "xsys/transition_system.h"

#include <algorithm>
#include <boost/algorithm/cxx11/all_of.hpp>
#include <cctype>

#include "supp/expr_rewriter.h"
#include "supp/expr_visitor.h"
#include "supp/expr_iterators.h"

#define EXIT_REGULATE EXIT_FAILURE

using namespace euforia;
using namespace std;

namespace {

bool string_balanced(const string& s) {
  vector<char> match;
  match.reserve(s.size());
  for (auto c : s) {
    if (c == '(')
      match.push_back(')');
    if (c == '[')
      match.push_back('[');
    if (c == '{')
      match.push_back('}');
    if (c == ')' || c == ']' || c == '}') {
      if (c == match.back())
        match.pop_back();
      else
        return false; // mismatched close
    }
  }
  return match.empty();
}

bool state_var_ok(const StateVar& v) {
  if (!(v.current().decl().name().str() + "+" ==
        v.next().decl().name().str())) {
    cerr << "next state not current with + suffix: " << v << "\n";
    return false;
  }

  if (!string_balanced(v.name()))
    return false;

  return true;
}

bool input_var_ok(const PrimaryInput& input) {
  if (input.name[input.name.size()-1] == '+') {
    cerr << "input name ends with +\n";
    return false;
  }

  if (!string_balanced(input.name)) {
    fmt::print(cerr, "input unbalanced parens: {}\n", input.name);
    return false;
  }

  return true;
}


class ExprOkPredicate
    : public ExprVisitor<ExprOkPredicate, bool> {
 public:
  bool operator()(const z3::expr& e) {
    return visit(e);
  }

  bool visitExpr(const z3::expr&) {
    return true;
  }

  // Sometimes creduce puts lots of things as equal
  bool visitEQ(const z3::expr& e) {
    if (!(e.num_args() == 2)) {
      cerr << "used n-ary equal\n";
      return false;
    }

    return true;
  }
};

bool expr_ok(const z3::expr& e) {
  ExprOkPredicate is_ok;
  bool b =  all_of(
      df_expr_iterator::begin(e), df_expr_iterator::end(e), is_ok);
  if (!b)
    cerr << "expr violation: " << e << "\n";
  return b;
}

} // end namespace


namespace euforia {

void CreduceRegulateTransitionSystem(const TransitionSystem& xsys) {
  if (!boost::algorithm::all_of(xsys.vars(), state_var_ok)) {
    cerr << "state var bad\n";
    goto fail;
  }
  if (!boost::algorithm::all_of(xsys.inputs(), input_var_ok)) {
    cerr << "input var bad\n";
    goto fail;
  }
  // too slow?
  // if (!expr_ok(xsys.init_state()) || !expr_ok(xsys.trans()) ||
  //     !expr_ok(xsys.property())) {
  //   goto fail;
  // }

  return;
fail:
  exit(EXIT_REGULATE);
}

} // end namespace euforia
