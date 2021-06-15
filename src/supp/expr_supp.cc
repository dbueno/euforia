// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/expr_supp.h"

#include <algorithm>
#include <boost/range/algorithm/transform.hpp>
#include <sstream>

#include "checker_types.h"
#include "supp/std_supp.h"
#include "abstract_model.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_iterators.h"




using namespace std;

void mylog(const euforia::ExprSet& s) {
  std::cerr << "set<";
  bool first = true;
  for (auto& e : s) {
    if (!first)
      std::cerr << " & ";
    std::cerr << e;
    first = false;
  }
  std::cerr << ">" << endl;
}

namespace z3 {
std::ostream& operator<<(std::ostream& os, const vector<z3::expr>& c) {
  os << "vector[" << c.size() << "]<";
  boost::copy(c, make_ostream_joiner(os, " & "));
  os << ">";
  return os;
}
std::ostream& operator<<(std::ostream& os, const euforia::ExprSet& c) {
  os << "unordered_set[" << c.size() << "]< ";
  boost::copy(c, make_ostream_joiner(os, " & "));
  os << ">";
  return os;
}
}

namespace euforia {

bool IsUFunction(const z3::func_decl& decl) {
  if (decl.decl_kind() == Z3_OP_UNINTERPRETED &&
      decl.arity() > 0 &&
      starts_with(decl.range().name().str(), uninterpreted_bv_sort_name))
    return true;
  
  return false;
}

bool IsUFunction(const z3::expr& e) {
  return IsUFunction(e.decl());
}

bool IsUPredicate(const z3::func_decl& decl) {
  if (decl.decl_kind() == Z3_OP_UNINTERPRETED &&
      decl.range().is_bool() &&
      decl.arity() > 0) {
    for (unsigned i = 0; i < decl.arity(); i++) {
      const auto& argSort = decl.domain(i);
      if (starts_with(argSort.name().str(), uninterpreted_bv_sort_name))
        return true;
    }
  }
  
  return false;
}


bool IsUninterp(const z3::expr& e) {
  return e.get_sort().sort_kind() == Z3_UNINTERPRETED_SORT;
}


bool IsLiteral(const z3::expr& l_in) {
  if (!l_in.is_bool())
    return false;
  for (auto it = df_expr_iterator::begin(l_in),
       ie = df_expr_iterator::end(l_in); it != ie; ++it) {
    switch ((*it).decl().decl_kind()) {
      case Z3_OP_AND:
      case Z3_OP_OR:
      case Z3_OP_XOR:
      case Z3_OP_ITE:
      case Z3_OP_IMPLIES:
      case Z3_OP_IFF:
        return false;

      case Z3_OP_NOT:
      case Z3_OP_EQ:
      case Z3_OP_DISTINCT:
        // toplevel equalities are ok, otherwise no
        if (!z3::eq(*it, l_in))
          return false;

      default:
        break;
    }
  }
  return true;
}


bool IsUConstant(const z3::func_decl& d) {
  return d.decl_kind() == Z3_OP_UNINTERPRETED && d.arity() == 0 && starts_with(d.name().str(), "$K");
}

z3::expr expr_and(const z3::expr& x, const z3::expr& y) {
  if (is_literal_true(x)) {
    return y;
  } else if (is_literal_true(y)) {
    return x;
  } else if (z3::eq(x, y)) {
    return x;
  } else {
    return x && y;
  }
}

z3::expr AndExprSet(z3::context& c, const ExprSet& s) {
  return expr_mk_and(c, s);
}

z3::expr expr_mk_and(z3::expr_vector v) {
  unsigned n = v.size();
  for (unsigned i = 0; i < n;) {
    assert(n>0);
    if (z3::eq(v[i], v[i].ctx().bool_val(true))) {
      auto last = v[--n];
      v.set(i, last);
    } else {
      i++;
    }
  }
  v.resize(n);
  if (v.size() == 0) {
    return v.ctx().bool_val(true);
  } else if (v.size() == 1) {
    return v[0];
  }
  return z3::mk_and(v);
}

z3::expr expr_mk_and(z3::context& c, const size_t n, const z3::expr *exprs) {
  z3::expr_vector v(c);
  copy(exprs, exprs + n, ExprVectorInserter(v));
  return expr_mk_and(v);
}

z3::expr expr_mk_or(z3::expr_vector v) {
  unsigned n = v.size();
  for (unsigned i = 0; i < n;) {
    assert(n>0);
    if (z3::eq(v[i], v[i].ctx().bool_val(false))) {
      auto last = v[--n];
      v.set(i, last);
    } else {
      i++;
    }
  }
  v.resize(n);
  if (v.size() == 0) {
    return v.ctx().bool_val(false);
  } else if (v.size() == 1) {
    return v[0];
  }
  return z3::mk_or(v);
}

z3::expr expr_or(const z3::expr& x, const z3::expr& y) {
  if (is_literal_false(x)) {
    return y;
  } else if (is_literal_false(y)) {
    return x;
  } else if (z3::eq(x, y)) {
    return x;
  } else {
    return x || y;
  }
}


/**
 * "smart" not that strips leading not and evaluates constants
 */
 z3::expr expr_not(const z3::expr& e) {
  assert(e.is_bool());
  const auto kind = e.decl().decl_kind();
  switch (kind) {
    case Z3_OP_TRUE:
      return e.ctx().bool_val(false);
    case Z3_OP_FALSE:
      return e.ctx().bool_val(true);
    case Z3_OP_NOT:
      return e.arg(0);
    case Z3_OP_EQ:
      if (e.num_args() == 2) {
        z3::expr_vector v(e.ctx());
        v.push_back(e.arg(0));
        v.push_back(e.arg(1));
        return expr_distinct(v);
      }
      return !e;
    case Z3_OP_DISTINCT:
      if (e.num_args() == 2) {
        // not(distinct(x, y)) is x == y
        return expr_eq(e.arg(0), e.arg(1));
      }
      return !e;
    default: return !e;
  }
}

z3::expr distribute_expr_not(const z3::expr& e) {
  if (e.is_or()) {
    z3::expr_vector conjuncts(e.ctx());
    boost::transform(ExprDisjuncts(e), ExprVectorInserter(conjuncts),
                     expr_not);
    return expr_mk_and(conjuncts);
  }
  return expr_not(e);
}


z3::expr expr_strip_negation(const z3::expr& e) {
  auto copy = e;
  if (is_not(copy))
    copy = copy.arg(0);
  assert(!is_not(copy)); // (not (not x)) should already have been x
  return copy;
}

z3::expr expr_eq(const z3::expr& a_in, const z3::expr& b_in) {
  auto a = (a_in.hash() < b_in.hash() ? a_in : b_in);
  auto b = (a_in.hash() < b_in.hash() ? b_in : a_in);
  if (z3::eq(a, b)) {
    return a.ctx().bool_val(true);
  } else if (a.is_bool()) {
    assert(b.is_bool());
    if (is_literal_true(a)) return b; // true == b  ==> b
    if (is_literal_true(b)) return a; // a == true  ==> a
    if (is_literal_false(a)) return expr_not(b); // false == a  ==> !b
    if (is_literal_false(b)) return expr_not(a);
  }
  
  return a == b;
}

z3::expr expr_distinct(const z3::expr& a, const z3::expr& b) {
  z3::expr_vector v(a.ctx());
  v.push_back(a);
  v.push_back(b);
  return expr_distinct(v);
}

z3::expr expr_distinct(const z3::expr_vector& v_in) {
  // sort the arguments, but can't use expr_vector because i would have to
  // create a special random access iterator to expr vectors that doesn't
  // return z3::expr&s but instead returns some kind of
  // z3_expr_ref_inside_vector
   vector<z3::expr> sortedArgs(begin(v_in), end(v_in));
   sort(begin(sortedArgs), end(sortedArgs),
               [](const z3::expr& a, const z3::expr& b) { return a.hash() < b.hash(); });
   z3::expr_vector v(v_in.ctx());
   for (auto& elt : sortedArgs) {
     v.push_back(elt);
   }

   if (v.size() == 1) {
     return v.ctx().bool_val(true);
   } else if (v.size() == 2) {
     auto x = v[0], y = v[1];
     assert(x.is_bool() == y.is_bool());
     if (z3::eq(x, x.ctx().bool_val(true))) {
       // distinct(true, y)  ==>  not(y)
       return expr_not(y);
     } else if (z3::eq(y, y.ctx().bool_val(true))) {
       // distinct(x, true)  ==>  not(x)
       return expr_not(x);
     } else if (z3::eq(x, x.ctx().bool_val(false))) {
       // distinct(false, y)  ==> y
       return y;
     } else if (z3::eq(y, y.ctx().bool_val(false))) {
       // distinct(x, false)  ==> x
       return x;
     }
  }
  
  return z3::distinct(v);
}

z3::expr expr_shl(const z3::expr& e, const z3::expr& b) {
  auto ret = Z3_mk_bvshl(Z3_context(e.ctx()), Z3_ast(e), Z3_ast(b));
  return z3::to_expr(e.ctx(), ret);
}

z3::expr expr_ashr(const z3::expr& e, const z3::expr& b) {
  auto ret = Z3_mk_bvashr(Z3_context(e.ctx()), Z3_ast(e), Z3_ast(b));
  return z3::to_expr(e.ctx(), ret);
}

z3::expr expr_lshr(const z3::expr& e, const z3::expr& b) {
  auto ret = Z3_mk_bvlshr(Z3_context(e.ctx()), Z3_ast(e), Z3_ast(b));
  return z3::to_expr(e.ctx(), ret);
}

z3::expr expr_zext_to(const z3::expr& e, unsigned newSize) {
  const auto sz = e.get_sort().bv_size();
  assert(newSize >= sz);
  if (newSize == sz)
    return e;

  return z3::zext(e, newSize-sz);
}

bool IsValue(const z3::expr& e) {
  if (e.num_args() == 0) {
    auto kind = e.decl().decl_kind();
    switch (kind) {
      case Z3_OP_BNUM:
      case Z3_OP_ANUM:
      case Z3_OP_TRUE:
      case Z3_OP_FALSE:
        return true;
        
      default:
        return false;
    }
  }
  return false;
}

z3::expr FreshBool(z3::context& ctx, const char *prefix) {
  return z3::to_expr(ctx, Z3_mk_fresh_const(ctx, prefix, ctx.bool_sort()));
}

z3::expr FreshBool(z3::context& ctx) {
  return FreshBool(ctx, "bool");
}


string SortName(const z3::sort& s) {
  stringstream ss;
  ss << s.name().str();
  if (s.is_bv()) {
    ss << s.bv_size();
  } else if (s.is_array()) {
    ss << "-" << SortName(s.array_domain());
    ss << "-" << SortName(s.array_range());
  }
  return ss.str();
}


struct height_of_expr : ExprRewriter<height_of_expr, size_t> {
  size_t visitExpr(const z3::expr& e) {
    size_t m = 0;
    for (unsigned i = 0; i < e.num_args(); i++) {
      m = 1+std::max(m, Arg(e,i));
    }
    return m;
  }
};






}
