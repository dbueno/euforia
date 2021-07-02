// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef mathsat_supp_hpp
#define mathsat_supp_hpp

#include "supp/expr_rewriter.h"
#include "checker_types.h"

#include <unordered_set>
#include <unordered_map>
#include <memory>
#include <llvm/ADT/GraphTraits.h>
#include <llvm/ADT/iterator.h>
#include <mathsat.h>
#include <gmpxx.h>

namespace euforia {
namespace mathsat {


class TermWrapper {
  msat_term t_;
  msat_env env_;
 
 public:
  
  TermWrapper() : env_({ .repr = nullptr }) {
    MSAT_MAKE_ERROR_TERM(t_);
  }
  
  TermWrapper(msat_env env, msat_term t) : t_(t), env_(env) {}

  TermWrapper(const TermWrapper& t) : t_(t.t_), env_(t.env_) {}
  
  TermWrapper& operator=(const TermWrapper& t) {
    t_ = t.t_;
    env_ = t.env_;
    return *this;
  }

  TermWrapper& operator=(const msat_term& t) {
    t_ = t;
    return *this;
  }

  inline operator msat_term() const { return t_; }

  bool is_error() const {
    return MSAT_ERROR_TERM(t_);
  }

  msat_env Env() const { return env_; }
  msat_term Term() const { return t_; }

  TermWrapper Arg(size_t i) const {
    return TermWrapper(env_, msat_term_get_arg(t_, i));
  }

  size_t NumArgs() const {
    return msat_term_arity(t_);
  }

  size_t Id() const {
    return msat_term_id(t_);
  }

  msat_symbol_tag Tag() const {
    return msat_decl_get_tag(env_, msat_term_get_decl(t_));
  }

  std::string Name() const {
    char *name = msat_decl_get_name(Decl());
    assert(name);
    auto ret = std::string(name);
    msat_free(name);
    return ret;
  }

  msat_decl Decl() const {
    return msat_term_get_decl(t_);
  }

  msat_type Type() const {
    return msat_decl_get_return_type(Decl());
  }

  bool IsArrayType(msat_type *idx_ty = nullptr,
                   msat_type *elt_ty = nullptr) const {
    return msat_is_array_type(env_, msat_decl_get_return_type(Decl()), idx_ty,
                              elt_ty);
  }

  bool IsBvType(size_t *width = nullptr) const {
    return msat_is_bv_type(env_, msat_decl_get_return_type(Decl()), width);
  }
    
  
  bool IsNumber() const {
    return msat_term_is_number(env_, t_);
  }

  std::string GetNumber(int base) const {
    // this is the only dependency on gmp and it's terrible
    mpq_t n;
    mpq_init(n);
    auto fail = msat_term_to_number(env_, t_, n);
    assert(!fail);
    _unused(fail);
    mpq_class n_class(n);
    return n_class.get_str(base);
  }

  //! test whether two terms are the same
  bool operator==(const TermWrapper& other) const {
    return Id() == other.Id();
  }

  void Print(std::ostream& os) const {
    auto str = msat_to_smtlib2(env_, t_);
    os << str;
    msat_free(str);
  }
};

std::ostream& operator<<(std::ostream& os, const TermWrapper& t);

}

struct HashTermWrapper {
  inline std::size_t operator()(const euforia::mathsat::TermWrapper& n) const {
    return std::hash<size_t>()(n.Id());
  }
};

struct EqualToTermWrapper {
  inline bool operator()(const euforia::mathsat::TermWrapper& a,
                         const euforia::mathsat::TermWrapper& b) const {
    return a.Id() == b.Id();
  }
};
}

//^----------------------------------------------------------------------------^
//

namespace euforia {
namespace mathsat {

class TermChildIterator : public llvm::iterator_facade_base<TermChildIterator,
    std::forward_iterator_tag, TermWrapper, size_t, TermWrapper*, TermWrapper> {
  TermWrapper t_;
  size_t i_;
 public:

  TermChildIterator(const TermWrapper& t) : t_(t), i_(0) {}
  TermChildIterator(const TermWrapper& t, size_t i) : t_(t), i_(i) {}
  TermChildIterator(const TermChildIterator& other)
      : t_(other.t_), i_(other.i_) {}
  TermChildIterator& operator=(const TermChildIterator& other) {
    t_ = other.t_;
    i_ = other.i_;
    return *this;
  }
  bool operator==(const TermChildIterator& other) const {
    return t_.Id() == other.t_.Id() && i_ == other.i_;
  }
  bool operator!=(const TermChildIterator& other) const {
    return !(*this == other);
  }

  TermWrapper operator*() { return t_.Arg(i_); }
  TermChildIterator& operator++() { ++i_; return *this; }
  TermChildIterator operator++(int) {
    TermChildIterator tmp = *this;
    ++*this;
    return tmp;
  }
};

}
}

//^----------------------------------------------------------------------------^
//

namespace llvm {
using euforia::mathsat::TermWrapper;
template <>
struct GraphTraits<TermWrapper> {
  using NodeRef = TermWrapper;
  using ChildIteratorType = euforia::mathsat::TermChildIterator;

  static NodeRef getEntryNode(const TermWrapper& n) { return n; }

  static ChildIteratorType child_begin(NodeRef n) {
    return euforia::mathsat::TermChildIterator(n);
  }
  static ChildIteratorType child_end(NodeRef n) {
    return euforia::mathsat::TermChildIterator(n, n.NumArgs());
  }
};
}

//^----------------------------------------------------------------------------^
//

namespace z3 {
class context;
}

namespace euforia {
class Statistics;

namespace mathsat {

template <typename SubClass, typename RetTy=void>
class TermVisitor {
 protected:
  TermVisitor() = default;
  ~TermVisitor() = default;

 public:
  
  RetTy Visit(const TermWrapper& e) {
    switch (e.Tag()) {
#define HANDLE_TAG(OP) case MSAT_TAG_##OP: \
      return static_cast<SubClass*>(this)->Visit##OP(e);

      HANDLE_TAG(TRUE);         /**< the Boolean constant True */
      HANDLE_TAG(FALSE);        /**< the Boolean constant False */
      HANDLE_TAG(AND);          /**< the AND Boolean connective */
      HANDLE_TAG(OR);           /**< the OR Boolean connective */
      HANDLE_TAG(NOT);          /**< the NOT Boolean connective */
      HANDLE_TAG(IFF);          /**< the IFF Boolean connective */
      HANDLE_TAG(PLUS);         /**< arithmetic addition */
      HANDLE_TAG(TIMES);        /**< arithmetic multiplication */
      HANDLE_TAG(DIVIDE);       /**< arithmetic division */
      HANDLE_TAG(FLOOR);        /**< floor function */
      HANDLE_TAG(LEQ);          /**< arithmetic <= */
      HANDLE_TAG(EQ);           /**< equality */
      HANDLE_TAG(ITE);          /**< term-level if-then-else */
      HANDLE_TAG(INT_MOD_CONGR);/**< integer modular congruence */
      HANDLE_TAG(BV_CONCAT);    /**< BV concatenation */
      HANDLE_TAG(BV_EXTRACT);   /**< BV selection */
      HANDLE_TAG(BV_NOT);       /**< BV bitwise not */
      HANDLE_TAG(BV_AND);       /**< BV bitwise and */
      HANDLE_TAG(BV_OR);        /**< BV bitwise or */
      HANDLE_TAG(BV_XOR);       /**< BV bitwise xor */
      HANDLE_TAG(BV_ULT);       /**< BV unsigned < */
      HANDLE_TAG(BV_SLT);       /**< BV signed < */
      HANDLE_TAG(BV_ULE);       /**< BV unsigned <= */
      HANDLE_TAG(BV_SLE);       /**< BV signed < */
      HANDLE_TAG(BV_COMP);      /**< BV bit comparison */
      HANDLE_TAG(BV_NEG);       /**< BV unary minus */
      HANDLE_TAG(BV_ADD);       /**< BV addition */
      HANDLE_TAG(BV_SUB);       /**< BV subtraction */
      HANDLE_TAG(BV_MUL);       /**< BV multiplication */
      HANDLE_TAG(BV_UDIV);      /**< BV unsigned division */
      HANDLE_TAG(BV_SDIV);      /**< BV signed division */
      HANDLE_TAG(BV_UREM);      /**< BV unsigned remainder */
      HANDLE_TAG(BV_SREM);      /**< BV signed remainder */
      HANDLE_TAG(BV_LSHL);      /**< BV logical left shift */
      HANDLE_TAG(BV_LSHR);      /**< BV logical right shift */
      HANDLE_TAG(BV_ASHR);      /**< BV arithmetic right shift */
      HANDLE_TAG(BV_ROL);       /**< BV rotate left */
      HANDLE_TAG(BV_ROR);       /**< BV rotate right */
      HANDLE_TAG(BV_ZEXT);      /**< BV zero extension */
      HANDLE_TAG(BV_SEXT);      /**< BV sign extension */
      HANDLE_TAG(ARRAY_READ);   /**< Array read/select operation */
      HANDLE_TAG(ARRAY_WRITE);  /**< Array write/store operation */
      HANDLE_TAG(ARRAY_CONST);  /**< Constant arrays */
      HANDLE_TAG(FP_EQ);        /**< FP IEEE equality */
      HANDLE_TAG(FP_LT);        /**< FP < */
      HANDLE_TAG(FP_LE);        /**< FP <= */
      HANDLE_TAG(FP_NEG);       /**< FP unary minus */
      HANDLE_TAG(FP_ADD);       /**< FP addition */
      HANDLE_TAG(FP_SUB);       /**< FP subtraction */
      HANDLE_TAG(FP_MUL);       /**< FP multiplication */
      HANDLE_TAG(FP_DIV);       /**< FP division */
      HANDLE_TAG(FP_SQRT);      /**< FP square root */
      HANDLE_TAG(FP_ABS);       /**< FP absolute value */
      HANDLE_TAG(FP_MIN);       /**< FP min */
      HANDLE_TAG(FP_MAX);       /**< FP max */
      HANDLE_TAG(FP_CAST);      /**< FP format conversion */
      HANDLE_TAG(FP_ROUND_TO_INT);/**<;FP round to integer */
      HANDLE_TAG(FP_FROM_SBV);  /**< FP conversion from a signed BV */
      HANDLE_TAG(FP_FROM_UBV);  /**< FP conversion from an unsigned BV */
      HANDLE_TAG(FP_TO_BV);     /**< FP conversion to BV */
      HANDLE_TAG(FP_AS_IEEEBV); /**< FP as IEEE BV (access to the bits) */
      HANDLE_TAG(FP_ISNAN);     /**< FP check for NaN */
      HANDLE_TAG(FP_ISINF);     /**< FP check for infinity */
      HANDLE_TAG(FP_ISZERO);    /**< FP check for zero */
      HANDLE_TAG(FP_ISSUBNORMAL)/**<;FP check for subnormal */
      HANDLE_TAG(FP_ISNORMAL);  /**< FP check for normal */
      HANDLE_TAG(FP_ISNEG);     /**< FP check for negative */
      HANDLE_TAG(FP_ISPOS);     /**< FP check for positive */
      HANDLE_TAG(FP_FROM_IEEEBV)/**<;FP conversion from IEEE BV */
      HANDLE_TAG(INT_FROM_UBV); /**< Unsigned BV -> INT conversion */
      HANDLE_TAG(INT_FROM_SBV); /**< Signed BV -> INT conversion */
      HANDLE_TAG(INT_TO_BV);     /**< INT -> BV conversion */
      HANDLE_TAG(FORALL);
      HANDLE_TAG(EXISTS);

      default:
        return static_cast<SubClass*>(this)->VisitTerm(e);
#undef HANDLE_TAG
      
    }
  }

  void VisitTerm(const TermWrapper&) {} // ignore

#define DELEGATE(TAG) RetTy Visit##TAG(const TermWrapper& e) { \
  return static_cast<SubClass*>(this)->VisitTerm(e); }
    DELEGATE(TRUE);          /**< the Boolean constant True */
    DELEGATE(FALSE);         /**< the Boolean constant False */
    DELEGATE(AND);           /**< the AND Boolean connective */
    DELEGATE(OR);            /**< the OR Boolean connective */
    DELEGATE(NOT);           /**< the NOT Boolean connective */
    DELEGATE(IFF);           /**< the IFF Boolean connective */
    DELEGATE(PLUS);          /**< arithmetic addition */
    DELEGATE(TIMES);         /**< arithmetic multiplication */
    DELEGATE(DIVIDE);        /**< arithmetic division */
    DELEGATE(FLOOR);         /**< floor function */
    DELEGATE(LEQ);           /**< arithmetic <= */
    DELEGATE(EQ);            /**< equality */
    DELEGATE(ITE);           /**< term-level if-then-else */
    DELEGATE(INT_MOD_CONGR); /**< integer modular congruence */
    DELEGATE(BV_CONCAT);     /**< BV concatenation */
    DELEGATE(BV_EXTRACT);    /**< BV selection */
    DELEGATE(BV_NOT);        /**< BV bitwise not */
    DELEGATE(BV_AND);        /**< BV bitwise and */
    DELEGATE(BV_OR);         /**< BV bitwise or */
    DELEGATE(BV_XOR);        /**< BV bitwise xor */
    DELEGATE(BV_ULT);        /**< BV unsigned < */
    DELEGATE(BV_SLT);        /**< BV signed < */
    DELEGATE(BV_ULE);        /**< BV unsigned <= */
    DELEGATE(BV_SLE);        /**< BV signed < */
    DELEGATE(BV_COMP);       /**< BV bit comparison */
    DELEGATE(BV_NEG);        /**< BV unary minus */
    DELEGATE(BV_ADD);        /**< BV addition */
    DELEGATE(BV_SUB);        /**< BV subtraction */
    DELEGATE(BV_MUL);        /**< BV multiplication */
    DELEGATE(BV_UDIV);       /**< BV unsigned division */
    DELEGATE(BV_SDIV);       /**< BV signed division */
    DELEGATE(BV_UREM);       /**< BV unsigned remainder */
    DELEGATE(BV_SREM);       /**< BV signed remainder */
    DELEGATE(BV_LSHL);       /**< BV logical left shift */
    DELEGATE(BV_LSHR);       /**< BV logical right shift */
    DELEGATE(BV_ASHR);       /**< BV arithmetic right shift */
    DELEGATE(BV_ROL);        /**< BV rotate left */
    DELEGATE(BV_ROR);        /**< BV rotate right */
    DELEGATE(BV_ZEXT);       /**< BV zero extension */
    DELEGATE(BV_SEXT);       /**< BV sign extension */
    DELEGATE(ARRAY_READ);    /**< Array read/select operation */
    DELEGATE(ARRAY_WRITE);   /**< Array write/store operation */
    DELEGATE(ARRAY_CONST);   /**< Constant arrays */
    DELEGATE(FP_EQ);         /**< FP IEEE equality */
    DELEGATE(FP_LT);         /**< FP < */
    DELEGATE(FP_LE);         /**< FP <= */
    DELEGATE(FP_NEG);        /**< FP unary minus */
    DELEGATE(FP_ADD);        /**< FP addition */
    DELEGATE(FP_SUB);        /**< FP subtraction */
    DELEGATE(FP_MUL);        /**< FP multiplication */
    DELEGATE(FP_DIV);        /**< FP division */
    DELEGATE(FP_SQRT);       /**< FP square root */
    DELEGATE(FP_ABS);        /**< FP absolute value */
    DELEGATE(FP_MIN);        /**< FP min */
    DELEGATE(FP_MAX);        /**< FP max */
    DELEGATE(FP_CAST);       /**< FP format conversion */
    DELEGATE(FP_ROUND_TO_INT);/**< FP round to integer */
    DELEGATE(FP_FROM_SBV);   /**< FP conversion from a signed BV */
    DELEGATE(FP_FROM_UBV);   /**< FP conversion from an unsigned BV */
    DELEGATE(FP_TO_BV);      /**< FP conversion to BV */
    DELEGATE(FP_AS_IEEEBV);  /**< FP as IEEE BV (access to the bits) */
    DELEGATE(FP_ISNAN);      /**< FP check for NaN */
    DELEGATE(FP_ISINF);      /**< FP check for infinity */
    DELEGATE(FP_ISZERO);     /**< FP check for zero */
    DELEGATE(FP_ISSUBNORMAL);/**< FP check for subnormal */
    DELEGATE(FP_ISNORMAL);   /**< FP check for normal */
    DELEGATE(FP_ISNEG);      /**< FP check for negative */
    DELEGATE(FP_ISPOS);      /**< FP check for positive */
    DELEGATE(FP_FROM_IEEEBV);/**< FP conversion from IEEE BV */
    DELEGATE(INT_FROM_UBV);  /**< Unsigned BV -> INT conversion */
    DELEGATE(INT_FROM_SBV);  /**< Signed BV -> INT conversion */
    DELEGATE(INT_TO_BV);     /**< INT -> BV conversion */
    DELEGATE(FORALL);
    DELEGATE(EXISTS);
#undef DELEGATE
};


//! Rewrites mathsat terms bottom up using a cache
template <typename SubClass, typename RetTy,
         typename SetTy=std::unordered_set<TermWrapper, HashTermWrapper,
         EqualToTermWrapper>>
class TermRewriter : public TermVisitor<SubClass, RetTy> {
  std::shared_ptr<std::unordered_map<TermWrapper, RetTy, HashTermWrapper,
      EqualToTermWrapper>> cache_;
  SetTy visited_;

 protected:
  using Iterator = llvm::po_ext_iterator<TermWrapper, SetTy>;
  
  TermRewriter() 
      : cache_(std::make_shared<std::unordered_map<TermWrapper, RetTy,
               HashTermWrapper, EqualToTermWrapper>>()) {}
  ~TermRewriter() = default;

  RetTy Arg(const TermWrapper& t, size_t i) {
    return cache_->at(t.Arg(i));
  }
  RetTy arg(const TermWrapper& t, size_t i) {
    return cache_->at(t.Arg(i));
  }

 public:
  struct Stats {
    int64_t num_visits_;
  };
  
  RetTy operator()(const TermWrapper& e) {
    for (auto it = Iterator::begin(e, visited_),
         ie = Iterator::end(e, visited_); it != ie; ++it) {
      const auto& top = *it;
      if (auto search = cache_->find(top); search != cache_->end())
        return search->second;
      ++stats_.num_visits_;
      auto ret = static_cast<SubClass*>(this)->Visit(top);
      cache_->insert({top, ret});
    }
    return cache_->at(e);
  }

 private:
  Stats stats_;
};

//^----------------------------------------------------------------------------^
//

class Z3TermRewriter : public TermRewriter<Z3TermRewriter, z3::expr> {
  z3::context& ctx_;

 public:
  Z3TermRewriter(z3::context& c) : ctx_(c), stats_{} {}

  inline z3::context& ctx() { return ctx_; }

  z3::sort TranslateType(msat_env env, msat_type ty);
  z3::expr VisitTerm(const TermWrapper&);

  z3::expr VisitTRUE(const TermWrapper&);
  z3::expr VisitFALSE(const TermWrapper&);
  z3::expr VisitAND(const TermWrapper& t);
  z3::expr VisitOR(const TermWrapper& t);
  z3::expr VisitNOT(const TermWrapper& t);
  z3::expr VisitIFF(const TermWrapper& t);
  z3::expr VisitPLUS(const TermWrapper& t);
  z3::expr VisitTIMES(const TermWrapper& t);
  z3::expr VisitDIVIDE(const TermWrapper& t);
  z3::expr VisitLEQ(const TermWrapper& t);
  z3::expr VisitEQ(const TermWrapper& t);
  z3::expr VisitITE(const TermWrapper& t);
  z3::expr VisitBV_CONCAT(const TermWrapper& t);
  z3::expr VisitBV_EXTRACT(const TermWrapper& t);
  z3::expr VisitBV_NOT(const TermWrapper& t);
  z3::expr VisitBV_AND(const TermWrapper& t);
  z3::expr VisitBV_OR(const TermWrapper& t);
  z3::expr VisitBV_XOR(const TermWrapper& t);
  z3::expr VisitBV_ULT(const TermWrapper& t);
  z3::expr VisitBV_SLT(const TermWrapper& t);
  z3::expr VisitBV_ULE(const TermWrapper& t);
  z3::expr VisitBV_SLE(const TermWrapper& t);
  z3::expr VisitBV_COMP(const TermWrapper& t);
  z3::expr VisitBV_NEG(const TermWrapper& t);
  z3::expr VisitBV_ADD(const TermWrapper& t);
  z3::expr VisitBV_SUB(const TermWrapper& t);
  z3::expr VisitBV_MUL(const TermWrapper& t);
  z3::expr VisitBV_UDIV(const TermWrapper& t);
  z3::expr VisitBV_SDIV(const TermWrapper& t);
  z3::expr VisitBV_UREM(const TermWrapper& t);
  z3::expr VisitBV_SREM(const TermWrapper& t);
  z3::expr VisitBV_LSHL(const TermWrapper& t);
  z3::expr VisitBV_LSHR(const TermWrapper& t);
  z3::expr VisitBV_ASHR(const TermWrapper& t);
  z3::expr VisitBV_ZEXT(const TermWrapper& t);
  z3::expr VisitBV_SEXT(const TermWrapper& t);
  z3::expr VisitARRAY_READ(const TermWrapper& t);
  z3::expr VisitARRAY_WRITE(const TermWrapper& t);
  z3::expr VisitARRAY_CONST(const TermWrapper& t);
  z3::expr VisitEXISTS(const TermWrapper&);

  struct Stats {
    int64_t num_array_read_;
    int64_t num_array_write_;
    int64_t num_store_of_store_;
    int64_t num_array_read_numeral_idx_;
    int64_t num_array_write_numeral_idx_;
    int64_t num_array_write_numeral_val_;
  };

  void collect_statistics(Statistics *st) const;

 private:
  Stats stats_;
};

}
}

void mylog(const euforia::mathsat::TermWrapper& t);


#endif
