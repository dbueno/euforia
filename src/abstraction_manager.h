// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef abstraction_manager_hpp
#define abstraction_manager_hpp

#include "checker_types.h"
#include "supp/expr_rewriter.h"
#include "abstract_model.h" // ConcreteFuncDeclMap

#include <propagate_const.h>


namespace euforia {

class Concretizer;
  
// This is the way we do abstraction. By rewriting all the equations.
class AbstractionManager
    : public ExprRewriter<AbstractionManager>,
      public ExprVisitor<AbstractionManager, z3::expr> {
 public:
  AbstractionManager(z3::context& c,
                     const ExprMap<z3::expr>& ground);
  AbstractionManager(const AbstractionManager&) = delete;
  AbstractionManager& operator=(const AbstractionManager&) = delete;
  ~AbstractionManager();
  
  const ExprSet& constants() const { return constants_; }
  
  const ConcreteFuncDeclMap& 
  decls() const { return reverse_func_decls_; }

  // Adds a ground sort substitution. Precondition: no abstraction for concrete
  // or concretizatino for abstract must already exist.
  void AddGroundAbstraction(const z3::expr& concrete, const z3::expr& abstract);
  
  z3::sort AbstractSort(const z3::sort& s) const;

  AstMap<z3::expr_vector> GetConstsBySort() const;
  
  z3::expr Abstract(const z3::expr& e);
  
  z3::expr Concretize(const z3::expr& e);
  

  // Below here is the implementation of the abstraction rewriter. Most of
  // the rewriting is similar so we macroize it.
  
  // Many abstractions are simply a UF of the appropriate name called on the
  // abstracted args

#define GENERIC_TO_UF(opName) \
  z3::expr visit##opName(const z3::expr& e) { \
    z3::expr_vector args(e.ctx()); \
    for (unsigned i = 0; i < e.num_args(); i++) { \
      args.push_back(Arg(e,i)); \
    } \
    return AbstractUf(#opName, e, e.get_sort(), e.decl(), args); \
  }
    
#define GENERIC_TO_UF1(opName, op) \
  z3::expr visit##opName(const z3::expr& e) { \
    z3::expr_vector args(e.ctx()); \
    for (unsigned i = 0; i < e.num_args(); i++) { \
      args.push_back(Arg(e,i)); \
    } \
    auto fun = [](const z3::expr_vector& args) -> z3::expr { \
      assert(args.size()==1); \
      auto ret = op(args[0]); \
      return ret; }; \
    return AbstractUf(#opName, e, e.get_sort(), fun, args); \
  }
    
#define GENERIC_TO_UF2(opName, funcName, op) \
  z3::expr visit##opName(const z3::expr& e) { \
    z3::expr_vector args(e.ctx()); \
    for (unsigned i = 0; i < e.num_args(); i++) { \
      args.push_back(Arg(e,i)); \
    } \
    auto fun = [](const z3::expr_vector& args) -> z3::expr { \
      assert(args.size()==2); \
      auto ret = op(args[0], args[1]); \
      return ret; }; \
    return AbstractUf(funcName, e, e.get_sort(), fun, args); \
  }
    
#define ASSOC_TO_UF(assocOp, op) \
  z3::expr visit##assocOp(const z3::expr& e) { \
    z3::expr_vector args(e.ctx()); \
    for (unsigned i = 0; i < e.num_args(); i++) { \
      args.push_back(Arg(e,i)); \
    } \
    auto fun = [](const z3::expr_vector& args) { \
      z3::expr ret = args[0]; \
      for (unsigned i = 1; i < args.size(); i++) { \
        ret = op(ret,args[i]); \
      } \
      return ret; \
    }; \
    return AbstractUf(#assocOp, e, e.get_sort(), fun, args); \
  }
    
  ASSOC_TO_UF(BADD, operator+);
  ASSOC_TO_UF(BSUB, operator-);
  ASSOC_TO_UF(BMUL, operator*);
  GENERIC_TO_UF2(BUDIV, "BUDIV", z3::udiv);
  GENERIC_TO_UF2(BUDIV_I, "BUDIV", z3::udiv);
  GENERIC_TO_UF2(BSDIV, "BSDIV", operator/);
  GENERIC_TO_UF2(BSDIV_I, "BSDIV", operator/);
  GENERIC_TO_UF2(BSMOD, "BSMOD", z3::smod); //operator%);
  GENERIC_TO_UF2(BSMOD_I, "BSMOD", z3::smod);
  GENERIC_TO_UF2(BUREM, "BUREM", z3::urem);
  GENERIC_TO_UF2(BUREM_I, "BUREM", z3::urem);
  GENERIC_TO_UF2(BSREM, "BSREM", z3::srem);
  GENERIC_TO_UF2(BSREM_I, "BSREM", z3::srem);
  GENERIC_TO_UF1(BNEG, operator-);
  
  z3::expr visitExpr(const z3::expr& e);
  
  z3::expr visitUNINTERPRETED(const z3::expr& n);
  
  z3::expr visitDISTINCT(const z3::expr& e);
  
  z3::expr visitSGT(const z3::expr& e);
  z3::expr visitUGT(const z3::expr& e);
  z3::expr visitSGEQ(const z3::expr&) { EUFORIA_FATAL("should not occur"); }
  z3::expr visitSLT(const z3::expr&) { EUFORIA_FATAL("should not occur"); };
  z3::expr visitSLEQ(const z3::expr&) { EUFORIA_FATAL("should not occur"); };
  z3::expr visitUGEQ(const z3::expr&) { EUFORIA_FATAL("should not occur"); };
  z3::expr visitULT(const z3::expr&) { EUFORIA_FATAL("should not occur"); };
  z3::expr visitULEQ(const z3::expr&) { EUFORIA_FATAL("should not occur"); };
  
  ASSOC_TO_UF(BOR, operator|);
  ASSOC_TO_UF(BAND, operator&);
  ASSOC_TO_UF(BXOR, operator^);
  GENERIC_TO_UF1(BNOT, operator~);
  GENERIC_TO_UF(BSHL);
  GENERIC_TO_UF(BLSHR);
  GENERIC_TO_UF(BASHR);
  
  
  z3::expr visitBNUM(const z3::expr& n);
  z3::expr visitEXTRACT(const z3::expr& e);
  z3::expr visitCONCAT(const z3::expr& e);
  z3::expr visitSIGN_EXT(const z3::expr& e);
  z3::expr visitZERO_EXT(const z3::expr& e);
  
  z3::expr visitSTORE(const z3::expr& e);
  z3::expr visitSELECT(const z3::expr& e);
  z3::expr visitCONST_ARRAY(const z3::expr& e);
    
    
#undef GENERIC_TO_UF
#undef ASSOC_TO_UF

  inline z3::context& ctx() const { return ctx_; }

  bool abstract_arrays() const { return abstract_arrays_; }
  void set_abstract_arrays(bool absarr = true) { abstract_arrays_ = absarr; }
  bool abstract_array_select_fresh() const { return abstract_array_select_fresh_; }
  void set_abstract_array_select_fresh(bool sf = true) { abstract_array_select_fresh_ = sf; }

 private:
  using ExprRewriter::Rewrite;
  friend class Concretizer;
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Concretizer>> concretizer_;
  
  // if new constants added since last abstraction
  bool dirty_ = true;
  
  z3::context& ctx_;
  
  // XXX use bimap
  ExprMap<z3::expr> subst_;   // ground substitution
  ExprMap<z3::expr> reverse_subst_; // reverse ground substitution
  
  // abstract func_decl -> concrete func_decl
  ConcreteFuncDeclMap reverse_func_decls_;
  
  // all constants seen
  ExprSet constants_;

  // If true, this class turns arrays into an uninterpreted constant; select
  // and store become UFs. If false, keeps arrays as term->term, which probably
  // won't work ever.
  bool abstract_arrays_;
  
  // If true, abstracts array select() terms as fresh uninterpreted 0-arity
  // terms instead of SELECT() UF.
  bool abstract_array_select_fresh_;
  
  z3::expr AbstractUf(const std::string& name, const z3::expr& n,
                      z3::sort sort,
                      std::function<z3::expr(const z3::expr_vector&)> decl,
                      const z3::expr_vector& args);
  z3::expr AbstractUfIntParams(const std::string& name, const z3::expr& e,
                       std::function<z3::expr(const z3::expr_vector&)> decl);
  z3::expr AbstractFresh(const std::string& name, z3::expr e);
};

}

#endif /* abstraction_manager_hpp */
