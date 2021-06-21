// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/expr_supp.h"

#include <algorithm>
#include <boost/range/algorithm/copy.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/range/algorithm/transform.hpp>
#include <llvm/ADT/PostOrderIterator.h>
#include <sstream>
#include <type_traits>

#include "abstract_model.h"
#include "checker_types.h"
#include "supp/expr_graph_traits.h"
#include "supp/expr_iterators.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_visitor.h"
#include "supp/std_supp.h"




using namespace std;
using namespace euforia::pp;
using namespace euforia;
using namespace euforia::pp;
using namespace llvm;

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





DocPtr PpExprCube(z3::expr c) {
  DocStream elts;
  elts << pp::groupsep(ExprConjunctIterator::begin(c),
                       ExprConjunctIterator::end(),
                       pp::group(pp::append(
                               pp::break_(1, 0),
                               pp::text("& ")
                               )));
  return pp::nest(4, elts);
}


} // namespace euforia

//^----------------------------------------------------------------------------^
// Pretty printing


namespace {
std::string ac_sep(z3::expr e) {
  return AcSep(e.decl().decl_kind());
}
}



namespace euforia {
class ExprPrinter;
class SharedAddrTraversal;
class SharedExprPrinter;
}
namespace llvm {
template <>
class po_iterator_storage<ExprPrinter, true> {
 public:
  inline po_iterator_storage(ExprPrinter& s) : ppexpr_(s) {}

  // Defined below
  void finishPostorder(z3::expr e);
  bool insertEdge(Optional<z3::expr> from, z3::expr to);

 private:
  ExprPrinter& ppexpr_;
};

template <>
class po_iterator_storage<SharedAddrTraversal, true> {
 public:
  inline po_iterator_storage(SharedAddrTraversal& s) : ppexpr_(s) {}

  // Defined below
  void finishPostorder(z3::expr e);
  bool insertEdge(Optional<z3::expr> from, z3::expr to);

 private:
  SharedAddrTraversal& ppexpr_;
};

template <>
class po_iterator_storage<SharedExprPrinter, true> {
 public:
  inline po_iterator_storage(SharedExprPrinter& s) : ppexpr_(s) {}

  // Defined below
  void finishPostorder(z3::expr e);
  bool insertEdge(Optional<z3::expr> from, z3::expr to);

 private:
  SharedExprPrinter& ppexpr_;
};
} // namespace llvm


//^----------------------------------------------------------------------------^

namespace euforia {

std::string AcSep(Z3_decl_kind k) {
  switch (k) {
    case Z3_OP_OR: return "||";
    case Z3_OP_AND: return "&&";
    case Z3_OP_BAND: return "&";
    case Z3_OP_BOR: return "|";
    case Z3_OP_BXOR: return "^";
    case Z3_OP_BADD: return "+bv";
    case Z3_OP_XOR: return "xor";
    case Z3_OP_ADD: return "+";
    case Z3_OP_MUL: return "*";
    case Z3_OP_CONCAT: return "@";

    default:
                     ENSURE(false);
  }
}

std::ostream& ExprLegend::PrintNode(std::ostream& os, const z3::expr& e) {
  std::stringstream ss;
  std::string s;
  if (e.is_numeral(s)) {
    fmt::print(ss, "{}", s);
  } else if (e.is_var()) {
    fmt::print(ss, "{}", e.to_string());
  } else if (e.is_quantifier()) {
    bool is_forall = Z3_is_quantifier_forall(e.ctx(), e);
    bool is_lambda = Z3_is_lambda(e.ctx(), e);

    ss << (is_lambda?"^":(is_forall?"!":"?")) << "[";

    const unsigned num_bound = Z3_get_quantifier_num_bound(e.ctx(), e);
    for (unsigned i = 0; i < num_bound; ++i) {
      Z3_symbol n = Z3_get_quantifier_bound_name(e.ctx(), e, i);
      auto sym = z3::symbol(e.ctx(), n);
      // z3::sort srt(e.ctx(), Z3_get_quantifier_bound_sort(e.ctx(), e, i));
      ss << sym.str() << ": ";
      // if (i + 1 < nb) {
      //   out << ", ";
      // }
    }
    ss << "] : ";

    fmt::print(ss, "{:08x} ", e.body().hash());
  } else {
    assert(e.is_app());
    for (const auto& a : ExprArgs(e)) {
      fmt::print(ss, "{:08x} ", a.hash());
    }
    fmt::print(os, "{:08x}: {} {}", e.hash(), e.decl().name().str(),
               ss.str());
  }
  return os;
}

std::ostream& ExprLegend::Print(std::ostream& os, const z3::expr& e) {
  for (auto it = po_expr_ext_iterator::begin(e, visited_),
       ie = po_expr_ext_iterator::end(e, visited_); it != ie; ++it) {
    PrintNode(os, *it);
    os << "\n";
  }
  return os;
}

class PpCache {
 public:

  class ArgIterator : public boost::iterator_facade<
        ArgIterator,
        const DocPtr,
        boost::forward_traversal_tag,
        const DocPtr> {
    public:
     ArgIterator(const ExprMap<DocPtr>* m, unsigned i, z3::expr e) : i_(i), m_(m), e_(e) {
       ENSURE(i <= e.num_args());
     }

    private:
     friend class boost::iterator_core_access;

     void increment() { i_++; }

     bool equal(const ArgIterator& other) const {
       return m_ == other.m_ && e_ == other.e_ && i_ == other.i_;
     }

     const DocPtr dereference() const { return m_->at(static_cast<z3::expr>(e_).arg(i_)); }

     unsigned i_;
     const z3::ExprWrapper e_;
     const ExprMap<DocPtr>* m_;
  };

  ArgIterator args_begin(z3::expr e) const { return ArgIterator(&m_, 0, e); }
  ArgIterator args_end(z3::expr e) const { return ArgIterator(&m_, e.num_args(), e); }

  DocPtr arg(unsigned i, z3::expr e) const { return m_.at(e.arg(i)); }

  void set_rewrite(z3::expr e, DocPtr d) { m_.insert({e, d}); }
  DocPtr rewrites_to(z3::expr e) const {
    ENSURE(has_rewrite(e));
    return m_.at(e);
  }
  bool has_rewrite(z3::expr e) const {
    return m_.find(e) != m_.end();
  }
  DocPtr at(z3::expr e) const {
    return m_.at(e);
  }

 private:
  ExprMap<DocPtr> m_;
};

class SortPrinter {
 public:
  DocPtr operator()(const z3::sort& s) {
    return visitSort(s);
  }

  DocPtr visitSort(const z3::sort& s) {
    _unused(s);
    return text("ANY-SORT");
  }

 private:
  SortMap<DocPtr> cache_;
};

//^----------------------------------------------------------------------------^

class ExprPrinter : public ExprVisitor<ExprPrinter, DocPtr> {
 private:
  PpCache cache_;
  vector<z3::expr> flatroots_;
  ExprLegend leg_;
  SortPrinter ppsort_;
  vector<string> names_;

 public:
  DocPtr operator()(const z3::expr& e) {
    if (logger.ShouldLog(7))
      leg_.Print(cerr, e);
    for (auto it = po_ext_begin(e, *this), ie = po_ext_end(e, *this);
         it != ie; ++it) {
      ; // work done in FinishPostorder and VisitPreorder
    }
    logger.Log(7, "flatroots");
    for (auto& e : flatroots_) {
      logger.Log(7, "{}", leg_.FormatNode(e));
    }
    ENSURE(flatroots_.empty());
    ENSURE(cache_.rewrites_to(e));
    return cache_.rewrites_to(e);
  }

  bool InsertEdge(Optional<z3::expr> from, z3::expr to) {
    auto push = [&](z3::expr e) {
      logger.Log(7, "push"); //, leg_.FormatNode(*from));
      flatroots_.push_back(e);
    };
    logger.Log(7, "InsertEdge: {:08x} -> {:08x}", from ? from->hash() : 0,
               to.hash());
    // This logic (along with what's in FinishPostorder) will print flattened
    // associative/commutative ops. This means (a && (b && (c && d))) will be
    // printed as (a && b && c && d). That way it prints with fewer parens and
    // less hierarchy, which is easier on the eyes.
    //
    // As the expr is explored top-down, on the first encounter of OP, we push
    // it into the flatroots_ list. In FinishPostorder (below), when we
    // encounter this member of flatroots, we rewrite it to its flattened
    // representation.
    if (to.is_app()) {
      switch (to.decl().decl_kind()) {
        case Z3_OP_OR:
        case Z3_OP_AND:
        case Z3_OP_BAND:
        case Z3_OP_BOR:
        case Z3_OP_BADD:
        case Z3_OP_BXOR:
        case Z3_OP_XOR:
        case Z3_OP_ADD:
        case Z3_OP_CONCAT:
          if (!from) {
            push(to);
          }
          if (from && from->decl().decl_kind() != to.decl().decl_kind()) {
            // to is a root because it isn't flattened into from
            push(to);
          }
          break;

        default:
          break;
      }
    }
    // Visits every edge.
    return true;
  }

  void FinishPostorder(z3::expr e) {
    // - if e is AND and has recorded children (i.e., it is the highest most AND
    // in its sequence), make a doc for it and all its children.
    // - otherwise, visit node
    DocPtr d;
    logger.Log(7, "FinishPostorder: {}", leg_.FormatNode(e));
    if (e.is_app()) {
      switch (e.decl().decl_kind()) {
        case Z3_OP_OR:
        case Z3_OP_AND:
        case Z3_OP_BAND:
        case Z3_OP_BOR:
        case Z3_OP_BADD:
        case Z3_OP_BXOR:
        case Z3_OP_XOR:
        case Z3_OP_ADD:
        case Z3_OP_CONCAT:
          ENSURE(!flatroots_.empty());
          if (z3::eq(flatroots_.back(), e)) {
            vector<DocPtr> kids;
            for (auto& e1 : ExprFlatKinds(e, e.decl().decl_kind())) {
              kids.push_back(cache_.rewrites_to(e1));
            }

            // This version breaks on *all* occurrences of the flattened
            // operator (if any need to break at all) which isn't maximally
            // space efficient but is actually possible to read.
            auto sep = append(line(), text(ac_sep(e)), text(" "));
            d = paren(nest_used(group(separate(kids.rbegin(), kids.rend(), sep))));
            logger.Log(7, "pop");
            flatroots_.pop_back();
          }
          break;

        default:
          d = visit(e);
      }
    } else {
      d = visit(e);
    }
    cache_.set_rewrite(e, d);
  }

  //^--------------------------------------------------------------------------^
  // visitors

  DocPtr visitExpr(const z3::expr& e) {
    string n;
    if (e.is_numeral(n)) {
      return text(n);
    }
    assert(e.is_app());
    for (auto arg : ExprArgs(e)) {
      ENSURE(cache_.has_rewrite(arg));
    }
    return text(e.to_string());
  }

  DocPtr visitUNINTERPRETED(const z3::expr& e) {
    if (e.num_args() == 0) {
      return visitExpr(e);
    }

    return append(
        {text(e.decl().name().str()),
        paren(nest_used(group(separate(cache_.args_begin(e), cache_.args_end(e),
                                       append(text(","), break_(1, 0))))))});
  }

  DocPtr visitQUANTIFIER(const z3::expr& e) {
    auto q = text(e.is_forall() ? "!" : "?");
    auto& ctx = e.ctx();
    // bool is_lambda = Z3_is_lambda(ctx, e);
    unsigned nb = Z3_get_quantifier_num_bound(ctx, e);

    vector<DocPtr> vars;
    for (unsigned i = 0; i < nb; ++i) {
      Z3_symbol n = Z3_get_quantifier_bound_name(ctx, e, i);
      z3::sort srt(ctx, Z3_get_quantifier_bound_sort(ctx, e, i));
      vars.push_back(append(
              {text(z3::symbol(ctx, n).str()),
              text(":"), ppsort_(srt)}));
    }
    return paren(append(
            {q,
            sepbox(vars.begin(), vars.end(), text("")), cache_.at(e.body())}));

  }

  DocPtr visitVAR(const z3::expr& e) {
    auto idx = Z3_get_index_value(e.ctx(), e);
    return text("var" + to_string(idx));
  }

#define BINOP_DOC(e, op)                \
  ENSURE((e).num_args() == 2);          \
  return paren(nest_used(group(append(  \
                  cache_.arg(0, (e)),   \
                  line(),               \
                  (op),                 \
                  line(),               \
                  cache_.arg(1, e)))));

  DocPtr visitEQ(const z3::expr& e) {
    return paren(nest_used(group(append(
                    cache_.arg(0, e),
                    line(),
                    text("="),
                    line(),
                    cache_.arg(1, e)))));
  }

  DocPtr visitIFF(const z3::expr& e) {
    return paren(nest_used(group(append(
                    cache_.arg(0, e),
                    line(),
                    text("iff"),
                    line(),
                    cache_.arg(1, e)))));
  }

  DocPtr visitDISTINCT(const z3::expr& e) {
    auto sep = append(line(), text("<>"), line());
    return paren(nest_used(group(separate(
                    cache_.args_begin(e),
                    cache_.args_end(e),
                    sep))));
  }

  DocPtr visitNOT(const z3::expr& e) {
    return append(text("~"), cache_.arg(0, e));
  }

  DocPtr visitITE(const z3::expr& e) {
    return paren(nest_used(group(append(
                    text("if: "), cache_.arg(0, e),
                    line(),
                    text("then: "), cache_.arg(1, e),
                    line(),
                    text("else: "), cache_.arg(2, e)))));
  }

  DocPtr visitIMPLIES(const z3::expr& e) {
    return paren(nest_used(group(append(
                    text("ante:"), cache_.arg(0, e),
                    line(),
                    text("implies:"), cache_.arg(1, e)))));
  }

  DocPtr visitSUB(const z3::expr& e) {
    BINOP_DOC(e, text("-"));
  }

  DocPtr visitUMINUS(const z3::expr& e) {
    return append(text("-"), cache_.arg(0, e));
  }

  DocPtr visitDIV(const z3::expr& e) {
    ENSURE(e.num_args() == 2);
    return paren(group(append(
        cache_.arg(0, e),
        text(" / "), cache_.arg(1, e))));
  }

  DocPtr visitIDIV(const z3::expr& e) {
    ENSURE(e.num_args() == 2);
    return paren(group(append(
        cache_.arg(0, e),
        text(" i/ "), cache_.arg(1, e))));
  }

  DocPtr visitREM(const z3::expr& e) {
    ENSURE(e.num_args() == 2);
    return paren(group(append(
        cache_.arg(0, e),
        text(" rem "), cache_.arg(1, e))));
  }

  DocPtr visitMOD(const z3::expr& e) {
    ENSURE(e.num_args() == 2);
    return paren(group(append(
        cache_.arg(0, e),
        text(" % "), cache_.arg(1, e))));
  }

  DocPtr visitLE(const z3::expr& e) {
    ENSURE(e.num_args() == 2);
    return paren(group(append(
        cache_.arg(0, e),
        text(" <= "), cache_.arg(1, e))));
  }

  DocPtr visitLT(const z3::expr& e) {
    ENSURE(e.num_args() == 2);
    return paren(group(append(
        cache_.arg(0, e),
        text(" < "), cache_.arg(1, e))));
  }

  DocPtr visitGE(const z3::expr& e) {
    ENSURE(e.num_args() == 2);
    return paren(group(append(
        cache_.arg(0, e),
        text(" >= "), cache_.arg(1, e))));
  }

  DocPtr visitGT(const z3::expr& e) {
    ENSURE(e.num_args() == 2);
    return paren(group(append(
        cache_.arg(0, e),
        text(" > "), cache_.arg(1, e))));
  }

  DocPtr visitSTORE(const z3::expr& e) {
    return paren(append(
            {cache_.arg(0, e),
            nest_used(group(brace(append(
                        {cache_.arg(1, e), break_(1, 0), text("<- "),
                        cache_.arg(2, e)}))))}));
  }

  DocPtr visitSELECT(const z3::expr& e) {
    return paren(append({cache_.arg(0, e), sqbracket(cache_.arg(1, e))}));
  }

  DocPtr visitCONST_ARRAY(const z3::expr& e) {
    return append(
        {text("(_ -> "), cache_.arg(0, e), text(")")});
  }

  DocPtr visitBSUB(const z3::expr& e) {
    BINOP_DOC(e, text("-bv"));
  }

  DocPtr visitBSDIV(const z3::expr& e) {
    BINOP_DOC(e, text("/bvs"));
  }

  DocPtr visitBUDIV(const z3::expr& e) {
    BINOP_DOC(e, text("/bvu"));
  }

  DocPtr visitBSREM(const z3::expr& e) {
    BINOP_DOC(e, text("bvsrem"));
  }

  DocPtr visitBUREM(const z3::expr& e) {
    BINOP_DOC(e, text("bvurem"));
  }

  DocPtr visitBSMOD(const z3::expr& e) {
    BINOP_DOC(e, text("\%bvs"));
  }

  DocPtr visitBSHL(const z3::expr& e) {
    BINOP_DOC(e, text("<<bv"));
  }

  DocPtr visitBASHR(const z3::expr& e) {
    BINOP_DOC(e, text(">>bva"));
  }

  DocPtr visitBLSHR(const z3::expr& e) {
    BINOP_DOC(e, text(">>bvl"));
  }

  DocPtr visitEXTRACT(const z3::expr& e) {
    // XXX special case extract with equal params
    ENSURE(e.num_args()==1);
    assert(Z3_get_decl_num_parameters(e.ctx(), e.decl()) == 2);
    auto hi = Z3_get_decl_int_parameter(e.ctx(), e.decl(), 0);
    auto lo = Z3_get_decl_int_parameter(e.ctx(), e.decl(), 1);
    if (hi == lo) {
      return append(
          {cache_.arg(0, e),
          sqbracket(nest_used(group(append(
                          {text("bit:"),
                          line(),
                          Pprint(hi)}))))});
    } else {
      return append(
          {cache_.arg(0, e),
          sqbracket(nest_used(group(append(
                          {text("frombit:"),
                          line(),
                          Pprint(hi),
                          line(),
                          text("downto:"),
                          line(),
                          Pprint(lo)}))))});
    }
  }

  DocPtr visitSIGN_EXT(const z3::expr& e) {
    assert(e.num_args()==1);
    assert(Z3_get_decl_num_parameters(e.ctx(), e.decl()) == 1);
    auto added_bits = Z3_get_decl_int_parameter(e.ctx(), e.decl(), 0);
    return paren(nest_used(group(append(
        {text("sext-to:"),
        Pprint(e.get_sort().bv_size() + added_bits),
        line(),
        text("of:"),
        line(),
        cache_.arg(0, e)}))));
  }

  DocPtr visitZERO_EXT(const z3::expr& e) {
    assert(e.num_args()==1);
    assert(Z3_get_decl_num_parameters(e.ctx(), e.decl()) == 1);
    auto added_bits = Z3_get_decl_int_parameter(e.ctx(), e.decl(), 0);
    return paren(nest_used(group(append(
        {text("zext-to:"),
        Pprint(e.get_sort().bv_size() + added_bits),
        line(),
        text("of:"),
        line(),
        cache_.arg(0, e)}))));
  }

  DocPtr visitSLT(const z3::expr& e) {
    BINOP_DOC(e, text("<s"));
  }

  DocPtr visitSLEQ(const z3::expr& e) {
    BINOP_DOC(e, text("<=s"));
  }

  DocPtr visitSGT(const z3::expr& e) {
    BINOP_DOC(e, text(">s"));
  }

  DocPtr visitSGEQ(const z3::expr& e) {
    BINOP_DOC(e, text(">=s"));
  }

  DocPtr visitULT(const z3::expr& e) {
    BINOP_DOC(e, text("<u"));
  }

  DocPtr visitULEQ(const z3::expr& e) {
    BINOP_DOC(e, text("<=u"));
  }

  DocPtr visitUGT(const z3::expr& e) {
    BINOP_DOC(e, text(">u"));
  }

  DocPtr visitUGEQ(const z3::expr& e) {
    BINOP_DOC(e, text(">=u"));
  }

  DocPtr visitBNEG(const z3::expr& e) {
    return append(text("bv-"), cache_.arg(0, e));
  }

  DocPtr visitBNOT(const z3::expr& e) {
    return append(text("bv~"), cache_.arg(0, e));
  }

  DocPtr visitBCOMP(const z3::expr& e) {
    return append(text("2comp"), cache_.arg(0, e));
  }

  DocPtr visitROTATE_LEFT(const z3::expr& e) {
    BINOP_DOC(e, text("lrot"));
  }

  DocPtr visitROTATE_RIGHT(const z3::expr& e) {
    BINOP_DOC(e, text("rrot"));
  }
};

//^----------------------------------------------------------------------------^


struct SharedNode {
  DocPtr addr;
  DocPtr doc;
  vector<DocPtr> args_addrs;
  int depth;
};

class SharedAddrTraversal : public ExprVisitor<ExprPrinter, DocPtr> {
 public:
  ExprMap<SharedNode> cache_;
  int counter_ = 0;

  ExprMap<SharedNode> operator()(const z3::expr& e) {
    for (auto it = po_ext_begin(e, *this), ie = po_ext_end(e, *this);
         it != ie; ++it) {
      ; // work done in FinishPostorder and VisitPreorder
    }
    return cache_;
  }

  void Build(z3::expr e) {
    _unused(e);
  }

  bool InsertEdge(Optional<z3::expr> from, z3::expr to) {
    _unused(from);
    if (cache_.find(to) == cache_.end()) {
      cache_[to];
      return true;
    }
    return false;
  }

  void FinishPostorder(z3::expr e) {
    SharedNode& n = cache_[e];
    if (e.num_args() == 0) {
      n.doc = n.addr = Pprint(e);
    } else {
      auto get_addr = [&](const z3::expr& e) { return cache_.at(e).addr; };
      n.addr = append(text("#"), text(fmt::format("{}", counter_++)));
      boost::copy(
          boost::make_iterator_range(
              boost::make_transform_iterator(ExprArgIterator::begin(e), get_addr),
              boost::make_transform_iterator(ExprArgIterator::end(e), get_addr)),
          back_inserter(n.args_addrs));
    }
  }

  DocPtr visitExpr(const z3::expr& e) {
    _unused(e);
    ENSURE(false);
  }
};

class SharedExprPrinter {
 public:
  // Maps to the "canonical" printed version.
  ExprMap<DocPtr> printed_;
  const ExprMap<SharedNode> share_;
  vector<DocPtr> out_;
  z3::expr e_;

  SharedExprPrinter(z3::expr e) : e_(e), share_(SharedAddrTraversal()(e)) {}

  DocPtr operator()() {
    printed_.clear();
    out_.clear();
    for (auto it = po_ext_begin(e_, *this), ie = po_ext_end(e_, *this);
         it != ie; ++it) {
      ; // work done in FinishPostorder and VisitPreorder
    }
    ENSURE(out_.size() == 1);
    // This is a knife.
    return out_.back();
  }

  bool InsertEdge(Optional<z3::expr> from, z3::expr to) {
    _unused(from);
    _unused(to);
    return true;
  }

  void FinishPostorder(z3::expr e) {
    ENSURE(out_.size() >= e.num_args());

    auto is_shared = [&](auto&& e) {
      bool b = (e.num_args() > 0 && !is_not(e) && share_.at(e).addr.use_count() >= 3);
      if (b)
        logger.Log(7, "{} use_count {} addr is {}", e, share_.at(e).addr.use_count(), share_.at(e).addr);
      return b;
    };

    // Pops arguments.
    vector<DocPtr> args_docs;
    for (unsigned i = 0; i < e.num_args(); i++) {
      args_docs.push_back(out_.back());
      logger.Log(7, "pop  <= {}", out_.back());
      out_.pop_back();
    }

    if (auto search = printed_.find(e); search == printed_.end()) {
      // Pretty-prints e for the first time. Creates the "canonical"
      // representation of e, not using an address for e (but kids from the out
      // stack).
      DocPtr d;
      if (e.num_args() == 0) {
        // If there aren't any arguments, this special case produces a term
        // that doesn't include empty parens on the end of the term (see else
        // case).
        d = append({text(e.decl().name().str())});
      } else {
        auto args_doc = nest(1, commabox(
                args_docs.rbegin(), args_docs.rend(),
                text(",")));
        d = append(
            {text(e.decl().name().str()), text("("), args_doc, text(")")});
      }
      // This formats the shared expression definition
      if (is_shared(e)) {
        d = append(text("#"), share_.at(e).addr, text(" is "), d);
      }
      out_.push_back(d);
      logger.Log(7, "push => {}", d);
      // Records that e's canonical version has been printed.
      printed_.insert({e, d});
    } else {
      // e has been pretty-printed before. We may (1) use an address for e or
      // (2) print it full again, depending on is_shared.
      if (is_shared(e)) {
        // If e is shared, formats it using its addr.
        out_.push_back(share_.at(e).addr);
        logger.Log(7, "push => {}", share_.at(e).addr);
      } else {
        out_.push_back(search->second);
        logger.Log(7, "push => {}", search->second);
      }
    }
  }
};

namespace pp {

DocPtr PpExpr(z3::expr e) {
  if (!bool(e)) {
    return text("null");
  }
  ExprPrinter pp;
  return pp(e);
}

DocPtr PpSharedExpr(z3::expr e) {
  if (!bool(e)) {
    return text("null");
  }
  SharedExprPrinter pp(e);
  return pp();
}

DocPtr PpFuncDecl(z3::func_decl d) {
  return text(d.to_string());
}

DocPtr PpFuncEntry(z3::func_entry entry) {
  auto sep = line();
  auto args = nest_used(group(separate(FuncEntryArgIterator(entry, 0), FuncEntryArgIterator(entry, entry.num_args()), sep)));
  return group(append(
          {text("if"),
          line(),
          args,
          line(),
          text("then"),
          line(),
          Pprint(entry.value())}));
}

DocPtr PpFuncInterp(z3::func_interp interp) {
  auto sep = line();
    auto entries = nest_used(group(
            separate(FuncInterpEntryIterator(interp, 0),
                     FuncInterpEntryIterator(interp, interp.num_entries()),
                     sep)));
  auto else_case = append(text("else -> "), Pprint(interp.else_value()));
  return group(append(
          {entries, line(), else_case}));
}

} // namespace pp

} // namespace euforia

// Implementation of po_iterator_storage methods.
namespace llvm {
bool po_iterator_storage<ExprPrinter, true>::insertEdge(
        Optional<z3::expr> from, z3::expr to) { return ppexpr_.InsertEdge(from, to); }
void po_iterator_storage<ExprPrinter, true>::finishPostorder(z3::expr e) { ppexpr_.FinishPostorder(e); }
bool po_iterator_storage<SharedAddrTraversal, true>::insertEdge(
        Optional<z3::expr> from, z3::expr to) { return ppexpr_.InsertEdge(from, to); }
void po_iterator_storage<SharedAddrTraversal, true>::finishPostorder(z3::expr e) { ppexpr_.FinishPostorder(e); }
bool po_iterator_storage<SharedExprPrinter, true>::insertEdge(
        Optional<z3::expr> from, z3::expr to) { return ppexpr_.InsertEdge(from, to); }
void po_iterator_storage<SharedExprPrinter, true>::finishPostorder(z3::expr e) { ppexpr_.FinishPostorder(e); }
} // namespace llvm


