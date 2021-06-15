// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef boolector_supp_hpp
#define boolector_supp_hpp

#include <boost/optional/optional.hpp>
#include <cstdio>
#include <functional>
#include <memory>

extern "C" {
#include "boolector.h"
}
#include "checker_types.h"
#include "supp/expr_rewriter.h"
#include "supp/optional_ref.h"
#include "xsys/state_vars.h"





namespace boolector {
using namespace euforia;
  

// wraps BoolectorNode* and arranges proper refcnts
class BoolectorNodeWrapper {
  friend class BtorWrapper;
  friend class BtorBvAssignment;
  friend class BtorArrayAssignment;
  
  Btor *c_btor_;
  BoolectorNode *c_node_;
  
  BoolectorNodeWrapper Wrap(BoolectorNode *n) const {
    return BoolectorNodeWrapper(btor(), n);
  }
  
 public:
  
  BoolectorNodeWrapper() : c_btor_(nullptr), c_node_(nullptr) {}
  BoolectorNodeWrapper(Btor *b, BoolectorNode *n) : c_btor_(b), c_node_(n) {}
  BoolectorNodeWrapper(const BoolectorNodeWrapper& n) 
      : c_btor_(n.c_btor_), c_node_(n.c_node_) {}
  BoolectorNodeWrapper& operator=(const BoolectorNodeWrapper& other) {
    c_btor_ = other.c_btor_;
    c_node_ = other.c_node_;
    return *this;
  }
  
  inline bool is_null() const { return c_node_ == nullptr; }
  
  std::string symbol() const {
    return std::string(boolector_get_symbol(btor(), c_node_));
  }
  inline int32_t id() const { return boolector_get_node_id(btor(), c_node_); }
  
  BoolectorSort sort() const { return boolector_get_sort(btor(), c_node_); }
  inline uint32_t width() const {
    auto ret = boolector_get_width(btor(), c_node_); return ret;
  }

  // unrelaible????
  //bool isVar() const { return boolector_is_var(btor(), c_node_); }
  bool isBV() const { return boolector_is_bitvec_sort(btor(), sort()); }
  bool isArray() const { return boolector_is_array_sort(btor(), sort()); }
  bool isFun() const { return boolector_is_fun_sort(btor(), sort()); }
  
  inline size_t hash() const {
    return std::hash<int>()(id());
  }
  

  inline Btor *btor() const { return c_btor_; }
  
  friend std::ostream& operator<<(std::ostream& os,
                                  const BoolectorNodeWrapper& n);
  
#define BTOR_DEFINE_BINOP(name, btor_fun) \
  inline BoolectorNodeWrapper name(const BoolectorNodeWrapper& other) const { \
    assert(btor() == other.btor()); \
    return Wrap(btor_fun(btor(), c_node_, other.c_node_)); \
  }

  BTOR_DEFINE_BINOP(operator==, boolector_eq);
  BTOR_DEFINE_BINOP(operator!=, boolector_ne);
  BTOR_DEFINE_BINOP(iff, boolector_iff);
  BTOR_DEFINE_BINOP(ne, boolector_ne);
  BTOR_DEFINE_BINOP(implies, boolector_implies);
  BTOR_DEFINE_BINOP(operator&&, boolector_and);
  BTOR_DEFINE_BINOP(operator&, boolector_and);
  BTOR_DEFINE_BINOP(operator||, boolector_or);
  BTOR_DEFINE_BINOP(operator|, boolector_or);
  BTOR_DEFINE_BINOP(operator^, boolector_xor);
  BTOR_DEFINE_BINOP(operator<, boolector_slt);
  BTOR_DEFINE_BINOP(operator<=, boolector_slte);
  BTOR_DEFINE_BINOP(operator>, boolector_sgt);
  BTOR_DEFINE_BINOP(operator>=, boolector_sgte);
  BTOR_DEFINE_BINOP(ult, boolector_ult);
  BTOR_DEFINE_BINOP(ulte, boolector_ulte);
  BTOR_DEFINE_BINOP(ugt, boolector_ugt);
  BTOR_DEFINE_BINOP(ugte, boolector_ugte);
  
  BTOR_DEFINE_BINOP(operator+, boolector_add);
  BTOR_DEFINE_BINOP(operator-, boolector_sub);
  BTOR_DEFINE_BINOP(operator*, boolector_mul);
  BTOR_DEFINE_BINOP(operator/, boolector_sdiv);
  BTOR_DEFINE_BINOP(udiv, boolector_udiv);
  BTOR_DEFINE_BINOP(operator%, boolector_smod);
  BTOR_DEFINE_BINOP(srem, boolector_srem);
  BTOR_DEFINE_BINOP(urem, boolector_urem);
  BTOR_DEFINE_BINOP(shl, boolector_sll);
  BTOR_DEFINE_BINOP(ashr, boolector_sra);
  BTOR_DEFINE_BINOP(lshr, boolector_srl);
  
  BTOR_DEFINE_BINOP(concat, boolector_concat);
  
#undef BTOR_DEFINE_BINOP
  
  inline BoolectorNodeWrapper slice(int hi, int lo) const {
    return Wrap(boolector_slice(btor(), c_node_, hi, lo));
  }
  
  inline BoolectorNodeWrapper sext(int addedbits) const {
    return Wrap(boolector_sext(btor(), c_node_, addedbits));
  }
  
  inline BoolectorNodeWrapper uext(int addedbits) const {
    return Wrap(boolector_uext(btor(), c_node_, addedbits));
  }
  
  inline BoolectorNodeWrapper operator!() const {
    return Wrap(boolector_not(btor(), c_node_));
  }
  inline BoolectorNodeWrapper operator~() const {
    return Wrap(boolector_not(btor(), c_node_));
  }
  inline BoolectorNodeWrapper negate() const {
    return Wrap(boolector_neg(btor(), c_node_));
  }
  
  friend BoolectorNodeWrapper ite(const BoolectorNodeWrapper& c,
                                  const BoolectorNodeWrapper& t,
                                  const BoolectorNodeWrapper& e);
  friend BoolectorNodeWrapper write(const BoolectorNodeWrapper& arr,
                                    const BoolectorNodeWrapper& c_node_,
                                    const BoolectorNodeWrapper& val);
  friend BoolectorNodeWrapper read(const BoolectorNodeWrapper& arr,
                                   const BoolectorNodeWrapper& c_node_);
  
  // apply
  BoolectorNodeWrapper operator()(const BoolectorNodeWrapper& a);
  BoolectorNodeWrapper operator()(
      const std::vector<BoolectorNodeWrapper>& args);
  friend BoolectorNodeWrapper apply(
      const std::vector<BoolectorNodeWrapper>& args, BoolectorNodeWrapper f);
  friend bool eq(const BoolectorNodeWrapper& e, const BoolectorNodeWrapper& f);
  
  
};
  
// test whether this node and the other are identical
inline bool eq(const BoolectorNodeWrapper& e, const BoolectorNodeWrapper& f) {
  return e.c_btor_ == f.c_btor_ && e.c_node_ == f.c_node_;
}

namespace {
struct HashBoolectorNodeWrapper {
  inline std::size_t operator()(const BoolectorNodeWrapper& n) const {
    return n.hash();
  }
};

struct EqualToBoolectorNodeWrapper {
  inline bool operator()(const BoolectorNodeWrapper& n,
                         const BoolectorNodeWrapper& m) const {
    return boolector::eq(n, m);
  }
};
}

std::size_t hash_value(const BoolectorNodeWrapper&);

using BoolectorNodeSet = std::unordered_set<BoolectorNodeWrapper,
      HashBoolectorNodeWrapper, EqualToBoolectorNodeWrapper>;



inline BoolectorNodeWrapper ite(const BoolectorNodeWrapper& c,
                                const BoolectorNodeWrapper& t,
                                const BoolectorNodeWrapper& e) {
  assert(c.btor() == t.btor() && t.btor() == e.btor());
  return BoolectorNodeWrapper(c.btor(), boolector_cond(c.btor(), c.c_node_,
                                                       t.c_node_, e.c_node_));
}

BoolectorNodeWrapper write(const BoolectorNodeWrapper& arr,
                           const BoolectorNodeWrapper& c_node_,
                           const BoolectorNodeWrapper& val);
BoolectorNodeWrapper read(const BoolectorNodeWrapper& arr,
                          const BoolectorNodeWrapper& c_node_);

BoolectorNodeWrapper apply(const std::vector<BoolectorNodeWrapper>& args,
                           BoolectorNodeWrapper f);


/*-----------------------------------------------------------------------------------*/

class BtorAssignment;

// wraps btor solver
class BtorWrapper {
  friend class boolector_model;
  // Stores each boolector leaf created because Boolector doesn't allow us to
  // create them twice, but this API does.
  std::unordered_map<std::string, BoolectorNodeWrapper> bools_;
  std::unordered_map<std::string, BoolectorNodeWrapper> bitvecs;
  std::unordered_map<std::string, BoolectorNodeWrapper> arrays;
  std::unordered_map<std::string, BoolectorNodeWrapper> params;
  std::vector<BoolectorNodeWrapper> funs;
  
  void add(BoolectorNode *n);
  void assume(BoolectorNode *n);

  FILE *trfp;

  BoolectorNodeWrapper Wrap(BoolectorNode *n) const {
    return BoolectorNodeWrapper(c_btor_, n);
  }

 public:
  Btor *c_btor_;
  std::vector<BoolectorNodeWrapper> assumptions;
  
  TimerDuration total_check_time_;
  TimerDuration total_simplify_time_;

  BtorWrapper();
  ~BtorWrapper();
  BtorWrapper(const BtorWrapper&); // clone

  Btor *btor() { return c_btor_; }

  // options
  void setOption(BtorOption o, uint32_t val);
  uint32_t getOption(BtorOption o) const;

  void PrintStats() const;
  void ResetStats();
  
  // assumptions
  void fixateAssumptions();
  void resetAssumptions();
  inline void assume(const BoolectorNodeWrapper& n) { assume(n.c_node_); }
  
  // node types

  BoolectorNodeWrapper zero(int width);

  BoolectorNodeWrapper bconst(const char *bits);

  BoolectorNodeWrapper bconst(const std::string& bits);

  BoolectorNodeWrapper boolVal(bool b);
  
  BoolectorNodeWrapper cint(int i, int width);

  BoolectorNodeWrapper boolvar(const std::string& name);

  BoolectorNodeWrapper var(int width, const std::string& name);

  BoolectorNodeWrapper uf(BoolectorSort s, const std::string& name);
  
  BoolectorNodeWrapper param(BoolectorSort sort, const std::string& name);
  
  BoolectorNodeWrapper fun(const std::vector<BoolectorNodeWrapper>& params,
                           BoolectorNodeWrapper body);
  
  BoolectorNodeWrapper array(const std::string& name, int ptrSize, int valWidth);

  BoolectorNodeWrapper const_array(int ptr_size,
                                   const BoolectorNodeWrapper& value);

  BoolectorNodeWrapper matchNode(const BoolectorNodeWrapper&) const;

  // sorts
  BoolectorSort fun_sort(BoolectorSort *params, uint32_t arity,
                         BoolectorSort ret);
  BoolectorSort array_sort(BoolectorSort index, BoolectorSort element);
  BoolectorSort bitvec_sort(uint32_t width);
  BoolectorSort bool_sort();
  
  // add assertion
  // XXX delete in favor of Add
  inline void add(const BoolectorNodeWrapper& n) { add(n.c_node_); }
  inline void Add(const BoolectorNodeWrapper& n) { add(n.c_node_); }
  
  // check
  enum class result { kSat, kUnsat, kUnknown };
  result simplify();
  result check();

  std::shared_ptr<BtorAssignment> assignment(const BoolectorNodeWrapper& n);
  BoolectorNodeWrapper assignmentNode(const BtorAssignment& a);
  
  void printModel() const;
  
  inline bool isFailed(const BoolectorNodeWrapper& n) const {
    return 1 == boolector_failed(c_btor_, n.c_node_);
  }
  
  template <typename lit_collection>
  BoolectorNodeSet
  failedLiterals(lit_collection lits) const {
    BoolectorNodeSet ret;
    for (auto lit : lits) {
      if (isFailed(lit)) {
        ret.insert(lit);
      }
    }
    return ret;
  }
  
  result checkSMT2(const std::string& filename);

  void setTrace(const std::string& filename);
  
  void DumpBenchmark(std::ostream& os) const;
  void Print(std::ostream& os) const;
  void printAssertions() const;
};



class Z3ToBtorRewriter : public ExprRewriter<Z3ToBtorRewriter,
    BoolectorNodeWrapper>,
    public ExprVisitor<Z3ToBtorRewriter, BoolectorNodeWrapper> {
  std::shared_ptr<BtorWrapper> B;
  
 public:
  explicit Z3ToBtorRewriter(std::shared_ptr<BtorWrapper>);

  inline std::shared_ptr<BtorWrapper> btor() const { return B; }

  BoolectorNodeWrapper visitExpr(const z3::expr& n);
  
  
#define DECLARE_HANDLER(KIND) \
BoolectorNodeWrapper visit##KIND(const z3::expr&);
  
  DECLARE_HANDLER(UNINTERPRETED);
  DECLARE_HANDLER(TRUE);
  DECLARE_HANDLER(FALSE);
  DECLARE_HANDLER(EQ);
  DECLARE_HANDLER(IFF);
  DECLARE_HANDLER(DISTINCT);
  DECLARE_HANDLER(NOT);
  DECLARE_HANDLER(AND);
  DECLARE_HANDLER(OR);
  DECLARE_HANDLER(XOR);
  DECLARE_HANDLER(ITE);
  DECLARE_HANDLER(IMPLIES);

  DECLARE_HANDLER(BNUM);
  DECLARE_HANDLER(BNOT);
  DECLARE_HANDLER(BIT2BOOL);
  DECLARE_HANDLER(BNEG);
  DECLARE_HANDLER(BADD);
  DECLARE_HANDLER(BSUB);
  DECLARE_HANDLER(BMUL);
  DECLARE_HANDLER(BSMOD);
  DECLARE_HANDLER(BSMOD_I);
  DECLARE_HANDLER(BSREM);
  DECLARE_HANDLER(BSREM_I);
  DECLARE_HANDLER(BUREM);
  DECLARE_HANDLER(BUREM_I);
  DECLARE_HANDLER(BUDIV);
  DECLARE_HANDLER(BUDIV_I);
  DECLARE_HANDLER(BSDIV);
  DECLARE_HANDLER(BSDIV_I);
  DECLARE_HANDLER(CONCAT);
  DECLARE_HANDLER(EXTRACT);
  DECLARE_HANDLER(SIGN_EXT);
  DECLARE_HANDLER(ZERO_EXT);
  DECLARE_HANDLER(SLT);
  DECLARE_HANDLER(SLEQ);
  DECLARE_HANDLER(SGT);
  DECLARE_HANDLER(SGEQ);
  DECLARE_HANDLER(ULT);
  DECLARE_HANDLER(ULEQ);
  DECLARE_HANDLER(UGT);
  DECLARE_HANDLER(UGEQ);
  DECLARE_HANDLER(BAND);
  DECLARE_HANDLER(BOR);
  DECLARE_HANDLER(BXOR);

  DECLARE_HANDLER(STORE);
  DECLARE_HANDLER(SELECT);
  DECLARE_HANDLER(CONST_ARRAY);
#undef DECLARE_HANDLER

 private:
  BoolectorSort TranslateSort(const z3::sort&) const;
};



std::ostream& operator<<(std::ostream& os, const BoolectorNodeWrapper& n);



class BtorAssignment {
 public:
  enum class kind {
    BV, Array
  };
  
  const enum kind kind;
  // may be null
  const char *symbol;
  
  BtorAssignment(const enum kind k, BtorWrapper& b, const char *symbol) 
      : kind(k), b(b), symbol(symbol) {}
  BtorAssignment(const BtorAssignment&) = delete;
  BtorAssignment& operator=(const BtorAssignment&) = delete;
  virtual ~BtorAssignment() = default;
  
  virtual bool operator==(const BtorAssignment& other) const = 0;
  virtual bool operator!=(const BtorAssignment& other) const {
    return !(*this == other);
  }
  
  virtual void print(std::ostream& os) const = 0;
  
  virtual bool isTrue() const { return false; }
  
  //! return this assignment as a z3 expr, using var as the base case (arrays
  // are defined in terms of a base case to store)
  virtual z3::expr AsExpr(const z3::expr& var) const = 0;

  virtual z3::expr AsConstraint(const z3::expr& var) const = 0;
  
  inline BoolectorNodeWrapper asNode() { return b.assignmentNode(*this); }
 
 protected:
  BtorWrapper& b;
};


class BtorArrayAssignment : public BtorAssignment {
 public:
  const unsigned ptrSize;
  const unsigned valSize;
  
  BtorArrayAssignment(BtorWrapper& b, const BoolectorNodeWrapper& n);
  ~BtorArrayAssignment() override;

  BtorArrayAssignment(const BtorArrayAssignment&) = delete;
  BtorArrayAssignment& operator=(const BtorArrayAssignment&) = delete;
  
  inline const std::vector<std::string>& indices() const { return indices_; }
  inline const std::vector<std::string>& values() const { return values_; }
  inline int size() const {
    assert(indices_.size() == values_.size());
    return static_cast<int>(indices_.size()); }
  
  virtual inline bool operator==(const BtorAssignment& other) const override {
    if (other.kind == kind) {
      auto& a = static_cast<const BtorArrayAssignment&>(other);
      return indices_ == a.indices_ && values_ == a.values_;
    }
    return false;
  }
  
  //! returns stores to the given array
  virtual z3::expr AsExpr(const z3::expr&) const override;
  //! constraints the given array with selects
  virtual z3::expr AsConstraint(const z3::expr&) const override;

  virtual void print(std::ostream& os) const override;

 private:
  // If present, this assignment represents a constant array
  boost::optional<std::string> const_value_;
  std::vector<std::string> indices_;
  std::vector<std::string> values_;
  std::vector<std::pair<std::string, std::string>> idx_val_pairs_;
  
};


class BtorBvAssignment : public BtorAssignment {
  const char *ass;
  
 public:
  const int width;

  BtorBvAssignment(BtorWrapper& b, const BoolectorNodeWrapper& n)
      : BtorAssignment(BtorAssignment::kind::BV, b,
                       boolector_get_symbol(n.btor(), n.c_node_)),
      ass(boolector_bv_assignment(n.btor(), n.c_node_)), width(n.width()) {
    assert(b.c_btor_ == n.btor());
  }
  BtorBvAssignment(const BtorBvAssignment&) = delete;
  BtorBvAssignment& operator=(const BtorBvAssignment&) = delete;
  
  ~BtorBvAssignment() override {
    boolector_free_bv_assignment(b.c_btor_, ass);
  }
  
  inline const char* value() const { return ass; }
  virtual bool isTrue() const override {
    assert(width == 1);
    return std::string("1") == ass;
  }
  
  virtual inline bool operator==(const BtorAssignment& other) const override {
    if (other.kind == kind) {
      return strcmp(ass, static_cast<const BtorBvAssignment&>(other).ass) == 0;
    }
    return false;
  }
  
  virtual z3::expr AsExpr(const z3::expr&) const override;
  
  virtual z3::expr AsConstraint(const z3::expr& var) const override;
  
  virtual void print(std::ostream& os) const override;

};

std::ostream& operator<<(std::ostream& os, const BtorAssignment& a);

}




void mylog(const boolector::BoolectorNodeWrapper& n);

#endif /* boolector_supp_hpp */
