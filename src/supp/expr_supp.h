// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno


#ifndef SUPP_EXPR_SUPP_H_
#define SUPP_EXPR_SUPP_H_

#include <z3++.h>

#include <boost/range/algorithm/copy.hpp>
#include <fmt/format.h>
#include <functional>
#include <map>
#include <set>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "supp/pp/doc.h"

// specific overloads for expr, sort, and func_decl even though they are ast's.
// this way pointers to such objects will be handled by these overloads in some
// cases, instead of fmt complaining that there is no specialization for these
// subclasses of ast.
template <>
struct fmt::formatter<z3::expr> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    if (it != end && *it != '}') {
      std::cerr << "invalid format\n";
      exit(1);
    }
    return it;
  }

  template <typename FormatContext>
  auto format(const z3::expr& e, FormatContext& ctx) -> decltype(ctx.out()) {
    return format_to(ctx.out(), "{}", euforia::pp::Pprint(e));
  }
};

template <>
struct fmt::formatter<z3::func_decl> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    if (it != end && *it != '}') {
      std::cerr << "invalid format\n";
      exit(1);
    }
    return it;
  }

  template <typename FormatContext>
  auto format(const z3::func_decl& f, FormatContext& ctx) -> decltype(ctx.out()) {
    return format_to(
        ctx.out(),
        "{}",
        f.to_string());
  }
};

template <>
struct fmt::formatter<z3::sort> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    if (it != end && *it != '}') {
      std::cerr << "invalid format\n";
      exit(1);
    }
    return it;
  }

  template <typename FormatContext>
  auto format(const z3::sort& f, FormatContext& ctx) -> decltype(ctx.out()) {
    return format_to(
        ctx.out(),
        "{}",
        f.to_string());
  }
};


namespace z3 {
/// Wraps a z3 expr so it can be used inside various collections. Equality,
/// hashing, and ordering have to be done properly.
class ExprWrapper {
 public:
  ExprWrapper(const z3::expr& e) : e_(e) {}
  ExprWrapper(z3::expr&& e) : e_(e) {}
  // convert implicitly back to z3::expr

  inline operator z3::expr() const { return e_; }

  inline bool operator==(const ExprWrapper& rhs) const {
    return z3::eq(e_, rhs.e_);
  }

  inline bool operator!=(const ExprWrapper& rhs) const {
    return !(*this == rhs);
  }

  inline std::size_t hash() const { return e_.hash(); }
  // arbitrary stable ordering
  inline bool operator<(const ExprWrapper& rhs) const {
    return hash() < rhs.hash();
  }

  z3::context& ctx() const { return e_.ctx(); }

 private:
  z3::expr e_;
};

struct HashExpr {
  inline std::size_t operator()(const ExprWrapper& a) const { return a.hash(); }
  inline std::size_t operator()(const z3::ast& a) const { return a.hash(); }
};

struct EqualToExpr {
  inline bool operator()(const ExprWrapper& a, const ExprWrapper& b) const {
    return a == b;
  }
  inline bool operator()(const ast& a, const ast& b) const {
    return eq(a, b);
  }
};

struct CompareAst {
  // Note: seems to be *worse* to compare on expr::id() than ast::hash().
  // Shrug.
  bool operator()(const ast& a, const ast& b) const {
    return a.hash() < b.hash();
  }
};

using CompareExpr = CompareAst;

// For boost hashing
inline std::size_t hash_value(const z3::expr& e) {
  return e.hash();
}

}

template <>
struct fmt::formatter<z3::ExprWrapper> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    if (it != end && *it != '}') {
      std::cerr << "invalid format\n";
      exit(1);
    }
    return it;
  }

  template <typename FormatContext>
  auto format(const z3::ExprWrapper& e, FormatContext& ctx) -> decltype(ctx.out()) {
    return format_to(
        ctx.out(),
        "{}",
        static_cast<z3::expr>(e).to_string());
  }
};

namespace euforia {
namespace pp {
//! Pretty prints an expression.
DocPtr PpExpr(z3::expr);
DocPtr PpFuncDecl(z3::func_decl);
DocPtr PpFuncEntry(z3::func_entry);
DocPtr PpFuncInterp(z3::func_interp);

//! Pretty prints an expression where some shared subterms are called out.
DocPtr PpSharedExpr(z3::expr);

template <>
struct PrettyPrinter<z3::expr> {
  DocPtr operator()(const z3::expr& e) { return PpExpr(e); }
};
template <>
struct PrettyPrinter<z3::func_decl> {
  DocPtr operator()(const z3::func_decl& e) const { return PpFuncDecl(e); }
};
template <>
struct PrettyPrinter<z3::func_entry> {
  DocPtr operator()(const z3::func_entry& e) const { return PpFuncEntry(e); }
};
template <>
struct PrettyPrinter<z3::func_interp> {
  DocPtr operator()(const z3::func_interp& e) const { return PpFuncInterp(e); }
};

template <>
struct PrettyPrinter<z3::ExprWrapper> {
  DocPtr operator()(const z3::ExprWrapper& e) { return PpExpr(e); }
};
} // namespace pp

//! Set of expressions. I'm careful to use z3::ExprWrapper here because if you
//! use == or != on sets, it will call x == y (for elements x and y from those
//! sets), instead of using the EqualToExpr. Because of the EqualityComparable
//! requirement in the c++ docs, I guess? I don't know.
//!
//! The main annoyance is you may not always be able to do
//!
//! for (auto& e : <set>) { e.expr_method() }
//!
//! instead you need to do:
//!
//! for (const z3::expr& e : <set>) { e.expr_method(); }
using ExprSet = std::unordered_set<z3::ExprWrapper, z3::HashExpr, z3::EqualToExpr>;
using OrderedExprSet = std::set<z3::ExprWrapper>;


//! Be wary when comparing with equality on maps (see comment on ExprSet
//! above).
template <typename T>
using ExprMap = std::unordered_map<z3::expr, T, z3::HashExpr, z3::EqualToExpr>;
template <typename T>
using OrderedExprMap = std::map<z3::ExprWrapper, T>;
template <typename T>
using ExprMultiMap = std::unordered_multimap<z3::ExprWrapper, T, z3::HashExpr, z3::EqualToExpr>;

template <typename T>
using AstMap = std::unordered_map<z3::ast, T, z3::HashExpr, z3::EqualToExpr>;
template <typename T>
using SortMap = std::unordered_map<z3::sort, T, z3::HashExpr, z3::EqualToExpr>;
template <typename T>
using FuncDeclMap = 
    std::unordered_map<z3::func_decl, T, z3::HashExpr, z3::EqualToExpr>;

}

namespace euforia {
// Whether it starts with uninterpreted_bv_sort_name
bool IsUninterp(const z3::expr&);
// Don't use this (2 functions). It relies on the name of the decl. Instead,
// use something else.
bool IsUFunction(const z3::func_decl&);
bool IsUFunction(const z3::expr&);
bool IsUPredicate(const z3::func_decl&);
inline bool IsUPredicate(const z3::expr& e) { return IsUPredicate(e.decl()); }
bool IsUConstant(const z3::func_decl& d);
inline bool IsTerm0(const z3::expr& e) {
  return e.is_app() && e.decl().decl_kind() == Z3_OP_UNINTERPRETED &&
      e.decl().arity() == 0;
}
// Whether e is a term standing for a concrete constant, $K-something
inline bool IsUConstant(const z3::expr& e) { return IsUConstant(e.decl()); }
// walks entire expression testing if it's a literal
bool IsLiteral(const z3::expr& l_in);
// concrete or abstract
bool IsValue(const z3::expr& e);

inline bool is_literal_true(const z3::expr& e) { return Z3_OP_TRUE == e.decl().decl_kind(); }
inline bool is_literal_false(const z3::expr& e) { return Z3_OP_FALSE == e.decl().decl_kind(); }
inline bool is_not(const z3::expr& e) { return e.decl().decl_kind() == Z3_OP_NOT; }
inline bool is_eq(const z3::expr& e) { return e.decl().decl_kind() == Z3_OP_EQ; }
inline bool is_distinct(const z3::expr& e) { return e.decl().decl_kind() == Z3_OP_DISTINCT; }
//! Returns true if the literal is a predicate about equality: =, (not =),
//! (distinct)
inline bool is_equality_lit(const z3::expr& e) { return is_eq(e) || (is_not(e) && is_eq(e.arg(0))) || is_distinct(e); }
inline bool is_or(const z3::expr& e) { return e.decl().decl_kind() == Z3_OP_OR; }
inline bool is_and(const z3::expr& e) { return e.decl().decl_kind() == Z3_OP_AND; }


// eagerly simplifying operators
z3::expr expr_and(const z3::expr& x, const z3::expr& y);
z3::expr AndExprSet(z3::context& c, const ExprSet& s);
z3::expr expr_or(const z3::expr& x, const z3::expr& y);
//! "smart" not that strips leading not and evaluates constants
z3::expr expr_not(const z3::expr& e);
//! Negates e, but distributes it over OR if e is an OR
z3::expr distribute_expr_not(const z3::expr& e);
inline z3::expr expr_id(const z3::expr& e) { return e; }
z3::expr expr_eq(const z3::expr& a, const z3::expr& b);
z3::expr expr_distinct(const z3::expr& a, const z3::expr& b);
z3::expr expr_distinct(const z3::expr_vector& v);
z3::expr expr_shl(const z3::expr& e, const z3::expr& b);
z3::expr expr_ashr(const z3::expr& e, const z3::expr& b);
z3::expr expr_lshr(const z3::expr& e, const z3::expr& b);
//! removes negation if there is one
z3::expr expr_strip_negation(const z3::expr& e);
//! zext e to the new size (better be >= e.size)
z3::expr expr_zext_to(const z3::expr& e, unsigned newSize);

z3::expr FreshBool(z3::context& ctx);
z3::expr FreshBool(z3::context& ctx, const char *prefix);

//! Returns a string that uniquely identifies the sort
std::string SortName(const z3::sort&);

template <typename Range>
bool is_valid(const Range& ante, const z3::expr& post) {
  z3::solver s(post.ctx());
  for (const auto& l : ante)
    s.add(l);
  s.add(!post);
  auto result = s.check();
  if (result != z3::check_result::unsat) {
    // std::cerr << s.get_model() << "\n";
    return false;
  }
  return true;
}

// checks that ante & post is sat
template <typename Range>
bool is_sat(const Range& ante, const z3::expr& post) {
  z3::solver s(post.ctx());
  for (const auto& l : ante)
    s.add(l);
  s.add(post);
  auto result = s.check();
  if (result != z3::check_result::sat) {
    return false;
  }
  return true;
}


//*-------------------------------------------------------------------------------*
//

//! Example: Make a collection c into a conjunction.
// z3::expr conjunction(ctx);
// std::copy(c.begin(), c.end(), ExprAndInserter(conjunction));
// use_conjunction(conjunctien);
class ExprAndInserter {
 public:
   using iterator_category = std::output_iterator_tag;
   using difference_type = void;
   using value_type = void;
   using pointer = void;
   using reference = void;

  inline explicit ExprAndInserter(z3::expr& e) : e_(e) {
    if (!bool(e_)) {
      e_ = e.ctx().bool_val(true);
    }
  }

  inline ExprAndInserter& operator=(const z3::expr& e) {
    e_ = expr_and(e_, e);
    return *this;
  }

  inline ExprAndInserter& operator*() { return *this; }
  inline ExprAndInserter& operator++() { return *this; }
  inline ExprAndInserter& operator++(int) { return *this; }

  z3::expr get() const { return e_; }
  // XXX remove this one
  inline z3::expr Get() const { return e_; }

 private:
  z3::expr& e_;
};


//! Example: Make a collection c into a disjunction.
// z3::expr disjunction(ctx);
// std::copy(c.begin(), c.end(), ExprOrInserter(disjunction));
//
// Example: Make a cube into a clause.
//
// z3::expr clause(ctx());
// std::transform(cube.begin(), cube.end(), ExprOrInserter(clause), expr_not);
class ExprOrInserter {
 public:
   using iterator_category = std::output_iterator_tag;
   using difference_type = void;
   using value_type = void;
   using pointer = void;
   using reference = void;

  inline explicit ExprOrInserter(z3::expr& e) : e_(e) {
    if (!bool(e_)) {
      e_ = e.ctx().bool_val(false);
    }
  }

  inline ExprOrInserter& operator=(const z3::expr& e) {
    e_ = expr_or(e_, e);
    return *this;
  }

  inline ExprOrInserter& operator*() { return *this; }
  inline ExprOrInserter& operator++() { return *this; }
  inline ExprOrInserter& operator++(int) { return *this; }

  inline z3::expr Get() const {
    return e_;
  }
  inline z3::expr get() const {
    return e_;
  }

 private:
  z3::expr& e_;
};


template <class T>
class AstVectorInserterT {
  public:
   using iterator_category = std::output_iterator_tag;
   using difference_type = void;
   using value_type = void;
   using pointer = void;
   using reference = void;

   inline explicit AstVectorInserterT(z3::ast_vector_tpl<T>& v) : v_(v) {}

   inline AstVectorInserterT& operator=(const T& e) {
     v_.push_back(e);
     return *this;
   }

   inline AstVectorInserterT& operator*() { return *this; }
   inline AstVectorInserterT& operator++() { return *this; }
   inline AstVectorInserterT& operator++(int) { return *this; }

  private:
  z3::ast_vector_tpl<T>& v_;
};


using AstVectorInserter = AstVectorInserterT<z3::ast>;
using SortVectorInserter = AstVectorInserterT<z3::sort>;
using ExprVectorInserter = AstVectorInserterT<z3::expr>;
using FuncDeclVectorInserter = AstVectorInserterT<z3::func_decl>;

using Z3EvalFunc = std::function<z3::expr(const z3::expr&, bool)>;

// Passes v to z3::mk_and, handling 0-length args.
z3::expr expr_mk_and(z3::expr_vector v);

z3::expr expr_mk_and(z3::context&, const size_t n, const z3::expr *exprs);

// Passes v to z3::mk_or, handling 0-length args.
z3::expr expr_mk_or(z3::expr_vector v);

// Copies the range to a vector
template <typename Range>
z3::expr expr_mk_and(z3::context& c, Range r) {
  z3::expr_vector v(c);
  boost::copy(r, ExprVectorInserter(v));
  return expr_mk_and(v);
}

// Copies the iterator to a vector
template <typename It>
z3::expr expr_mk_and(z3::context& c, It begin, It end) {
  z3::expr_vector v(c);
  std::copy(begin, end, ExprVectorInserter(v));
  return expr_mk_and(v);
}

template <typename Range>
z3::expr expr_mk_or(z3::context& c, Range r) {
  z3::expr_vector v(c);
  boost::copy(r, ExprVectorInserter(v));
  return expr_mk_or(v);
}

//^----------------------------------------------------------------------------^
// Pretty printing

//! Pretty prints an expression assuming it's a cube, i.e., ANDs of literals.
pp::DocPtr PpExprCube(z3::expr c);

//! Separator for associative commutative operators
std::string AcSep(Z3_decl_kind);

//! Prints expressions using their hashes and their decl names and uses a
//! visited set so we don't print anything twice
class ExprLegend {
 public:
  //! Formats a single node
  std::string FormatNode(const z3::expr& e) {
    std::stringstream ss;
    PrintNode(ss, e);
    return ss.str();
  }

  //! Prints a single node
  std::ostream& PrintNode(std::ostream& os, const z3::expr& e);

  //!  Prints an expression and all its descendents in post order
  std::ostream& Print(std::ostream& os, const z3::expr& e);

  inline void Reset() {
    visited_.clear();
  }

 private:
  ExprSet visited_;
};

} // namespace euforia


#endif
