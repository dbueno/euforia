// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef abstract_model_hpp
#define abstract_model_hpp

#include <memory>
#include <propagate_const.h>
#include <z3++.h>

#include "supp/expr_supp.h"
#include "supp/expr_visitor.h"
#include "supp/solver.h"


namespace euforia {
class Cube;
class TransitionSystem;

// abstract func_decl -> concrete func_decl
using ConcreteFuncDeclMap =
    AstMap<std::function<z3::expr(const z3::expr_vector&)>>;

class AbstractModel;

// represents (a consistent subpartition of) the partition of terms induced by a model
class UninterpretedPartition {
 public:
  UninterpretedPartition(AbstractModel& m) : model_(m) {}
  ~UninterpretedPartition();

  /*--------------------------------------------------------------------------*/
  
  int size() const;
  
  // tell about expression
  void Insert(const z3::expr&, bool model_completion = true);
  
  // test for same set
  bool Same(const z3::expr&, const z3::expr&) const;
  
  // get normalized representative term (NOT a TERM!val! thing)
  z3::expr Find(const z3::expr&) const;
  
  // equivalence class of term
  const ExprSet& CellFor(const z3::expr& term) const;
  
  // efficient formula representation of the partition
  ExprSet AsFormula() const;
  
  // removes all terms from cells that match pred
  void RemoveIf(const std::function<bool(const z3::expr&)>& pred);
  
  std::ostream& Print(std::ostream& os) const;
  
 private:
  AbstractModel& model_;
  ExprMap<ExprSet> cells_; // TERM!val!3 -> all terms we know about in this class
  
  z3::expr FindConstantIfPossible(const z3::expr&) const;

};

inline std::ostream& operator<<(std::ostream& os,
                                const UninterpretedPartition& UP) {
  return UP.Print(os);
}


/*-----------------------------------------------------------------------------------*/

// Our models include the solver's model as well as a complete partition of uninterpreted terms
// Also a traversal of the COI to get things properly
class AbstractModel : public ExprVisitor<AbstractModel, void> {
 public:

  AbstractModel(const std::shared_ptr<Model>& model, const TransitionSystem& TS,
                const ConcreteFuncDeclMap *func_decls_ = nullptr,
                bool populateDecls = false);
  AbstractModel(const AbstractModel&) = delete;
  ~AbstractModel();

  const Model& model() const {
    return *model_;
  }
  
  // evaluates the expression and caches the result (with some short-circuiting)
  z3::expr Eval(const z3::expr&, bool model_completion = false);

  //! test whether model satisfies the term
  bool Satisfies(const z3::expr&, bool model_completion = true);
  
  // Add expression to this slice of the whole model
  void Add(const z3::expr& e);

  void AddInputPredicate(const z3::expr& e);
  inline const ExprSet& input_predicates() {
    return input_predicates_;
  }

  inline z3::context& ctx(); 
  inline const z3::context& ctx() const;

  inline const UninterpretedPartition& partition() const { return upart_; }
  
  // Filter stuff back for projection (inputs, aux vars, UFs, next-state
  // vars) and write out expansion into Cube
  void ExpandIntoCube(Cube& out);
  
  
  bool shouldPrintFuncInterp = false;
  std::ostream& Print(std::ostream& os) const;

  unsigned num_evals() const;
  
  // overrides
  void visitExpr(const z3::expr&);

 private:
  const TransitionSystem& TS;
  std::shared_ptr<Model> model_;
  /// contains the calls to the UPs in the polarity of the model
  ExprSet upreds_; // all bool-valued
  UninterpretedPartition upart_;
  ExprSet preds_; // other atomic truths
  ExprSet input_predicates_;
  // during traversal we look for these, if present
  const ConcreteFuncDeclMap *func_decls_;
  
  class Impl;
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;
};

inline std::ostream& operator<<(std::ostream& os, const AbstractModel& AM) { return AM.Print(os); }


}

#endif /* abstract_model_hpp */
