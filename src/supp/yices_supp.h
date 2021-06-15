// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_YICES_SUPP_H_
#define EUFORIA_SUPP_YICES_SUPP_H_

extern "C" {
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <yices.h>
}

#include <gmpxx.h>
#include <iostream>
#include <llvm/ADT/iterator.h>
#include <sstream>
#include <vector>
#include <z3++.h>

#include "supp/expr_rewriter.h"
#include "supp/expr_visitor.h"
#include "supp/std_supp.h"


namespace euforia {
namespace yices_supp {
using namespace std;

// Use this so that we can define operator<< and graph traits
struct TermWrapper {
  TermWrapper() : t(NULL_TERM) {}
  TermWrapper(term_t t) : t(t) {}
  term_t t;
  operator term_t() const { return t; }
};

// Use this so that we can define operator<<
struct TypeWrapper {
  TypeWrapper(type_t t) : t(t) {}
  type_t t;
  operator type_t() const { return t; }
};

std::ostream& operator<<(std::ostream& os, const TermWrapper& t);

std::ostream& operator<<(std::ostream& os, const TypeWrapper& t);

class TermWrapperArgIterator 
    : public llvm::iterator_facade_base<
      TermWrapperArgIterator, std::forward_iterator_tag, TermWrapper, size_t,
      TermWrapper*, TermWrapper> {
 public:
  inline static TermWrapperArgIterator begin(const TermWrapper& t) {
    return TermWrapperArgIterator(t, 0);
  }
  inline static TermWrapperArgIterator end(const TermWrapper& t) {
    return TermWrapperArgIterator(t, yices_term_num_children(t.t));
  }

  inline bool operator==(const TermWrapperArgIterator& it) const {
    return t_ == it.t_ && i_ == it.i_;
  }

  inline bool operator!=(const TermWrapperArgIterator& it) const {
    return !(*this == it);
  }
  
  inline const TermWrapper operator*() const {
    return TermWrapper(yices_term_child(t_, i_));
  }
  inline TermWrapper operator*() {
    return TermWrapper(yices_term_child(t_, i_));
  }
  inline TermWrapperArgIterator& operator++() { ++i_; return *this; }
  inline TermWrapperArgIterator operator++(int) {
    TermWrapperArgIterator tmp = *this;
    ++*this;
    return tmp;
  }

 private:
  term_t t_;
  int32_t i_;

  TermWrapperArgIterator(const TermWrapper& t, int32_t i) : t_(t), i_(i) {}
  TermWrapperArgIterator& operator=(const TermWrapperArgIterator& it) {
    t_ = it.t_;
    i_ = it.i_;
    return *this;
  }
};

//^----------------------------------------------------------------------------^

class Z3YicesExprPair {
 public:
  Z3YicesExprPair(const z3::expr& e, TermWrapper t) : e_(e), t_(t) {}

  inline z3::expr z3_node() const { return e_; }
  inline operator z3::expr() const { return e_; }
  inline TermWrapper yices_node() const { return t_; }
  inline operator TermWrapper() const { return t_; }

 private:
  z3::expr e_;
  TermWrapper t_;
};

//^----------------------------------------------------------------------------^


class Z3ToYicesRewriter 
    : public ExprRewriter<Z3ToYicesRewriter, term_t>,
      public ExprVisitor<Z3ToYicesRewriter, term_t> {
 public:
  Z3ToYicesRewriter(int32_t& ci, ExprMap<term_t>& consts,
                    std::vector<z3::expr>& consts_by_i)
      : const_index_(ci), consts_(consts), consts_by_index_(consts_by_i) {}

  Z3YicesExprPair operator()(const z3::expr& e) {
    return Z3YicesExprPair(e, Rewrite(e));
  }

  term_t Rewrite(const z3::expr& e) {
    auto r = ExprRewriter::Rewrite(e);
    logger.Log(5, "z3 expr {} written in yices as\n{}", e, TermWrapper(r));
    return r;
  }
  
  // overrides
  inline term_t VisitAndCache(z3::expr top) {
    auto ret = ExprRewriter::VisitAndCache(top);
    assert(ret != -1);
    return ret;
  }

  term_t visitExpr(const z3::expr&) {
    EUFORIA_FATAL("should be specially implemented");
  }

  TypeWrapper TranslateSort(const z3::sort& s) {
    type_t ty;
    switch (s.sort_kind()) {
      case Z3_BOOL_SORT:
        ty = yices_bool_type();
        break;
      case Z3_BV_SORT:
        ty = yices_bv_type(s.bv_size());
        break;
      case Z3_ARRAY_SORT: {
        type_t dom_ty[] = {TranslateSort(s.array_domain())};
        ty = yices_function_type(1, dom_ty, TranslateSort(s.array_range()));
        break;
      }
      case Z3_UNINTERPRETED_SORT: {
        auto ty_name = s.name().str();
        ty = yices_get_type_by_name(ty_name.c_str());
        if (ty == NULL_TYPE) {
          ty = yices_new_uninterpreted_type();
          yices_set_type_name(ty, ty_name.c_str());
        }
        break;
      }
      default:
        EUFORIA_FATAL("unhandled sort");
    }
    return TypeWrapper(ty);
  }

  term_t visitUNINTERPRETED(const z3::expr& e) {
    // TranslateSort does the bulk of differentiation between different
    // scenarios here. Handles Boolean vars, uninterpret terms and predicates,
    // bit vector, and array variables.
    auto e_decl = e.decl();
    auto e_sort = e.get_sort();
    auto e_name = e_decl.name().str();
    TermWrapper f;
    // If e is an uninterpreted term with 0 arity that represents a constant
    // (i.e. starts with $K), we use yices_constant because it gives us
    // distinctness "for free."
    if (e.get_sort().sort_kind() == Z3_UNINTERPRETED_SORT &&
        starts_with(e_name, "$K") && // hack
        e_decl.arity() == 0) {
      if (auto search = consts_.find(e); search == consts_.end()) {
        logger.Log(5, "Z3ToYicesRewriter creating new distinct constant");
        f = yices_constant(TranslateSort(e.get_sort()), const_index_);
        assert(const_index_ == static_cast<int32_t>(consts_by_index_.size()));
        consts_by_index_.push_back(e);
        auto b = consts_.insert({e, f}).second;
        assert(b);
        const_index_++;
      }
      f = consts_.at(e);
      yices_set_term_name(f, e_name.c_str());
    } else {
      // handles Booleans, BVs, and function sorts
      vector<type_t> domain;
      domain.reserve(e_decl.arity());
      for (unsigned i = 0; i < e_decl.arity(); i++) {
        domain.push_back(TranslateSort(e_decl.domain(i)));
      }
      auto ty = TranslateSort(e_decl.range());
      if (e_decl.arity() != 0) {
        ty = yices_function_type(domain.size(), domain.data(), ty);
      }
      f = yices_new_uninterpreted_term(ty);
      yices_set_term_name(f, e_name.c_str());
      if (e_decl.arity() != 0) {
        vector<term_t> args = NewArgs(e);
        args.reserve(e_decl.arity());
        f = yices_application(f, args.size(), args.data());
      }
    }
    assert(f != -1);
    return f;
  }

  term_t visitCONST_ARRAY(const z3::expr&) {
    EUFORIA_FATAL("unsupported z3 node CONST_ARRAY");
  }

#define YICES_LOGIC_OPS_HANDLER(KIND, FUNC) \
  term_t visit##KIND(const z3::expr& n) { \
    vector<term_t> term_args = NewArgs(n); \
    return FUNC(term_args.size(), term_args.data()); \
  }

#define YICES_BV_LOGIC_OPS_HANDLER(KIND, FUNC) \
  term_t visit##KIND(const z3::expr& n) { \
    vector<term_t> term_args = NewArgs(n); \
    term_t ret = FUNC(term_args.size(), term_args.data()); \
    assert(yices_term_bitsize(ret) == n.get_sort().bv_size()); \
    return ret; \
  }


  YICES_LOGIC_OPS_HANDLER(DISTINCT, yices_distinct);
  YICES_LOGIC_OPS_HANDLER(AND, yices_and);
  YICES_LOGIC_OPS_HANDLER(OR, yices_or);
  YICES_LOGIC_OPS_HANDLER(XOR, yices_xor);

  term_t visitTRUE(const z3::expr&) {
    return yices_true();
  }

  term_t visitFALSE(const z3::expr&) {
    return yices_false();
  }

  term_t visitNOT(const z3::expr& n) {
    assert(n.num_args() == 1);
    return yices_not(Arg(n,0));
  }

#define YICES_BINARY_HANDLER(KIND, EXPR) \
  term_t visit##KIND(const z3::expr& n) { \
    assert(n.num_args() == 2); \
    auto x = Arg(n, 0), y = Arg(n, 1); \
    term_t ret = EXPR; \
    assert(!n.is_bv() || yices_term_is_bitvector(ret)); \
    assert(!n.is_bv() || \
           (static_cast<unsigned>(yices_term_bitsize(ret)) == \
            n.get_sort().bv_size())); \
    assert(!n.is_bool() || (yices_term_is_bool(ret))); \
    return ret; \
  }

#define YICES_TERNARY_HANDLER(KIND, EXPR) \
  term_t visit##KIND(const z3::expr& n) { \
    assert(n.num_args() == 3); \
    term_t ret = EXPR; \
    auto ytbs = yices_term_bitsize(ret); \
    assert(!yices_term_is_bitvector(ret) || ytbs > 0); \
    assert(!n.is_bv() || (static_cast<unsigned>(ytbs) == n.get_sort().bv_size())); \
    assert(!n.is_bool() || (yices_term_is_bool(ret))); \
    return ret; \
  }

#define YICES_RASSOC_HANDLER(KIND, COP) \
  term_t visit##KIND(const z3::expr& n) { \
    term_t ret = Arg(n,0); \
    for (unsigned i = 1; i < n.num_args(); i++) { \
      ret = COP(ret, Arg(n,i)); \
    } \
    return ret; \
  }

  YICES_BINARY_HANDLER(EQ, yices_eq(x, y));
  YICES_BINARY_HANDLER(IFF, yices_iff(x, y));
  YICES_TERNARY_HANDLER(ITE, yices_ite(Arg(n, 0), Arg(n, 1), Arg(n, 2)));
  YICES_BINARY_HANDLER(IMPLIES, yices_implies(x, y));

  // *** bit vector

  term_t visitBNUM(const z3::expr& n) {
    string numstr;
    auto b = n.is_numeral(numstr);
    assert(b);
    mpz_class num(numstr);
    string binstr = num.get_str(2);
    assert(binstr.size() <= n.get_sort().bv_size());
    string bits(n.get_sort().bv_size(), '0');
    copy(binstr.begin(), binstr.end(),
         bits.begin() + (bits.size() - binstr.size()));
    assert(bits.size() == n.get_sort().bv_size());
    return yices_parse_bvbin(bits.c_str());
  }

  YICES_BV_LOGIC_OPS_HANDLER(CONCAT, yices_bvconcat);

  term_t visitEXTRACT(const z3::expr& e) {
    // extract in z3 uses "parameters" not "arguments" to specify the hi and lo for extracting
    assert(Z3_get_decl_num_parameters(Z3_context(e.ctx()),
                                      Z3_func_decl(e.decl())) == 2);
    auto hi = Z3_get_decl_int_parameter(Z3_context(e.ctx()),
                                        Z3_func_decl(e.decl()), 0);
    auto lo = Z3_get_decl_int_parameter(Z3_context(e.ctx()),
                                        Z3_func_decl(e.decl()), 1);
    auto tgt = Arg(e, 0);
    auto ret = yices_bvextract(tgt, lo, hi);
    assert(yices_term_bitsize(ret) == e.get_sort().bv_size());
    return ret;
  }

  term_t visitSIGN_EXT(const z3::expr& e) {
    assert(Z3_get_decl_num_parameters(e.ctx(), e.decl()) == 1);
    auto added_bits = Z3_get_decl_int_parameter((e.ctx()), (e.decl()), 0);
    auto tgt = Arg(e, 0);
    auto ret = yices_sign_extend(tgt, added_bits);
    assert(yices_term_bitsize(ret) == e.get_sort().bv_size());
    return ret;
  } 

  term_t visitZERO_EXT(const z3::expr& e) {
    assert(Z3_get_decl_num_parameters(e.ctx(), e.decl()) == 1);
    auto added_bits = Z3_get_decl_int_parameter((e.ctx()), (e.decl()), 0);
    auto tgt = Arg(e, 0);
    auto ret = yices_zero_extend(tgt, added_bits);
    assert(yices_term_bitsize(ret) == e.get_sort().bv_size());
    return ret;
  }

  term_t visitBNOT(const z3::expr& n) {
    assert(n.num_args() == 1);
    term_t ret = yices_bvnot(Arg(n,0));
    assert(yices_term_bitsize(ret) == n.get_sort().bv_size());
    return ret;
  }

  term_t visitBNEG(const z3::expr& n) {
    assert(n.num_args() == 1);
    term_t ret = yices_bvneg(Arg(n,0));
    assert(yices_term_bitsize(ret) == n.get_sort().bv_size());
    return ret;
  }

  YICES_BINARY_HANDLER(BSUB, yices_bvsub(x, y));
  YICES_BINARY_HANDLER(BMUL, yices_bvmul(x, y));
  YICES_BINARY_HANDLER(BUDIV, yices_bvdiv(x, y));
  YICES_BINARY_HANDLER(BUDIV_I, yices_bvdiv(x, y));
  YICES_BINARY_HANDLER(BSDIV, yices_bvsdiv(x, y));
  YICES_BINARY_HANDLER(BSDIV_I, yices_bvsdiv(x, y));
  YICES_BINARY_HANDLER(BSMOD, yices_bvsmod(x, y));
  YICES_BINARY_HANDLER(BSMOD_I, yices_bvsmod(x, y));
  YICES_BINARY_HANDLER(BSREM, yices_bvsrem(x, y));
  YICES_BINARY_HANDLER(BSREM_I, yices_bvsrem(x, y));
  YICES_BINARY_HANDLER(BUREM, yices_bvrem(x, y));
  YICES_BINARY_HANDLER(BUREM_I, yices_bvrem(x, y));
  YICES_BINARY_HANDLER(SLT, yices_bvslt_atom(x, y));
  YICES_BINARY_HANDLER(SLEQ, yices_bvsle_atom(x, y));
  YICES_BINARY_HANDLER(SGT, yices_bvsgt_atom(x, y));
  YICES_BINARY_HANDLER(SGEQ, yices_bvsge_atom(x, y));
  YICES_BINARY_HANDLER(ULT, yices_bvlt_atom(x, y));
  YICES_BINARY_HANDLER(ULEQ, yices_bvle_atom(x, y));
  YICES_BINARY_HANDLER(UGT, yices_bvgt_atom(x, y));
  YICES_BINARY_HANDLER(UGEQ, yices_bvge_atom(x, y));

  term_t visitBADD(const z3::expr& n) {
    term_t ret = Arg(n,0);
    for (unsigned i = 1; i < n.num_args(); i++) {
      ret = yices_bvadd(ret, Arg(n,i));
    }
    assert(static_cast<unsigned>(yices_term_bitsize(ret)) == 
           n.get_sort().bv_size());
    return ret;
  }

  YICES_BV_LOGIC_OPS_HANDLER(BXOR, yices_bvxor);
  YICES_BV_LOGIC_OPS_HANDLER(BAND, yices_bvand);
  YICES_BV_LOGIC_OPS_HANDLER(BOR, yices_bvor);

  YICES_BINARY_HANDLER(BSHL, yices_bvshl(x, y));
  YICES_BINARY_HANDLER(BASHR, yices_bvashr(x, y));
  YICES_BINARY_HANDLER(BLSHR, yices_bvlshr(x, y));

  YICES_BINARY_HANDLER(SELECT, yices_application1(x, y));
  term_t visitSTORE(const z3::expr& n) {
    return yices_update1(Arg(n, 0), Arg(n, 1), Arg(n, 2));
  }


  #undef YICES_LOGIC_OPS_HANDLER
  #undef YICES_BV_LOGIC_OPS_HANDLER
  #undef YICES_BINARY_HANDLER
  #undef YICES_TERNARY_HANDLER
  #undef YICES_RASSOC_HANDLER

 private:
  int32_t& const_index_;
  ExprMap<term_t>& consts_;
  std::vector<z3::expr>& consts_by_index_;
};

} // namespace yices_supp
} // namespace euforia


namespace llvm {
using namespace euforia::yices_supp;
template <>
class GraphTraits<TermWrapper> {
 public:
  using NodeRef = TermWrapper;
  using ChildIteratorType = TermWrapperArgIterator;

  static NodeRef getEntryNode(const TermWrapper& t) { return t; }

  static ChildIteratorType child_begin(NodeRef n) {
    return TermWrapperArgIterator::begin(n);
  }

  static ChildIteratorType child_end(NodeRef n) {
    return TermWrapperArgIterator::end(n);
  }
};
} // namespace llvm


namespace euforia {
namespace yices_supp {

//^----------------------------------------------------------------------------^

#define CHECK_YICES_ERROR(r) \
    if (r == -1) throw std::runtime_error(yices_error_string());

class YicesToZ3Rewriter 
    : public Rewriter<YicesToZ3Rewriter, TermWrapper, z3::expr,
                      std::unordered_set<term_t>,
                      std::unordered_map<term_t, z3::expr>> {
 public:
  YicesToZ3Rewriter(z3::context& c,
                    const std::vector<z3::expr>& consts_by_index)
      : ctx_(c), consts_by_index_(consts_by_index) {}

  z3::expr operator()(term_t t) {
    switch (yices_term_constructor(t)) {
#define HANDLE_TERM(CONSTRUCTOR) \
      case YICES_##CONSTRUCTOR: return Visit##CONSTRUCTOR(t);

      HANDLE_TERM(BOOL_CONSTANT);
      HANDLE_TERM(SCALAR_CONSTANT);
      HANDLE_TERM(UNINTERPRETED_TERM);

      default:
        return VisitTerm(t);
    }
  }

  z3::expr VisitTerm(term_t t) { (void)t; EUFORIA_FATAL("unimplemented"); }

  z3::expr VisitBOOL_CONSTANT(term_t b) {
    int32_t val;
    CHECK_YICES_ERROR(yices_bool_const_value(b, &val));
    return ctx().bool_val(val == 1);
  }

  z3::expr VisitUNINTERPRETED_TERM(term_t t) {
    (void)t;
    EUFORIA_FATAL("not yet implemented");
  }

  z3::expr VisitSCALAR_CONSTANT(term_t t) {
    logger.Log(5, "VisitSCALAR_CONSTANT {}", TermWrapper(t));
    // Stores the index of constant in val
    int32_t val;
    CHECK_YICES_ERROR(yices_scalar_const_value(t, &val));
    return consts_by_index_[val];
  }

  inline z3::context& ctx() { return ctx_; }
 
 private:
  z3::context& ctx_;
  const std::vector<z3::expr>& consts_by_index_;
};

} // namespace yices_supp
} // namespace euforia

void mylog(const euforia::yices_supp::TermWrapper& t);
void mylog(const euforia::yices_supp::TypeWrapper&);
#endif
