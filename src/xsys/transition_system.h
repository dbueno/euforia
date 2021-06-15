// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_XSYS_TRANSITION_SYSTEM_H_
#define EUFORIA_XSYS_TRANSITION_SYSTEM_H_

#include <boost/optional/optional.hpp>
#include <boost/iterator/iterator_facade.hpp>
#include <boost/range/iterator_range.hpp>
#include <numeric>
#include <string>
#include <map>

#include "supp/expr_rewriter.h"
#include "supp/expr_substitution.h"
#include "supp/ip_rep.h"
#include "supp/optional_ref.h"
#include "xsys/primary_inputs.h"
#include "xsys/state_vars.h"



namespace euforia {

class AbstractModel;
class CheckerSat;
struct TSlice;
class Statistics;


// ========= master superclass for transition systems
class TransitionSystem {
 public:
  template <class T>
  using VarMap = std::map<std::string, T>;

  virtual ~TransitionSystem() = default;

  inline z3::expr init_state() const { return init_state_; }
  inline void set_init_state(const z3::expr& i) { init_state_ = i; }
  inline z3::expr property() const { return property_; }
  inline void set_property(const z3::expr& p) { property_ = p; }
  virtual z3::expr trans() const = 0;

  using EquationMapRef = std::reference_wrapper<const ExprMultiMap<z3::expr>>;
  //! Returns the part of the transition relation represented as equations.
  //! Note that trans() is still the real transition relation.
  virtual boost::optional<EquationMapRef> trans_equations() const {
    return boost::optional<EquationMapRef>();
  }
  //! Returns the part of the transition relation not represented as equations
  virtual z3::expr trans_rest() const {
    return trans();
  }

  void operator=(const TransitionSystem& x) = delete;

  inline const z3::params& simplify_params() const { return simplify_params_; }

  inline const IpRepr& ip_repr() const { return ip_; }


  // Building the system =======================================================

  // Next state vars end with '+'
  // Location vars start with '@'
  // Abstract vars start with '^'

  const StateVar& AddVar(std::unique_ptr<StateVar> v);
  virtual void DeleteVar(const std::string& name);

  inline OptionalRef<const StateVar> FindVar(const std::string& name) const {
    OptionalRef<const StateVar> ret;
    if (auto search = vars_.find(name); search != vars_.end()) {
      ret = *search->second;
    }
    return ret;
  }
  
  inline OptionalRef<const StateVar> FindVar(const z3::expr& e) const {
    OptionalRef<const StateVar> ret;
    if (auto search = expr2var_.find(e); search != expr2var_.end()) {
      ret = search->second;
    }
    return ret;
  }
  
  inline bool HasCurrentStateVar(const z3::expr& e) const {
    if (auto v = FindVar(e)) {
      return z3::eq(v->current(), e);
    }
    return false;
  }
  
  inline bool HasNextStateVar(const z3::expr& e) const {
    if (auto v = FindVar(e)) {
      return z3::eq(v->next(), e);
    }
    return false;
  }
  
  const PrimaryInput& AddInput(std::unique_ptr<PrimaryInput> inp);
  virtual void DeleteInput(const std::string& name);

  inline OptionalRef<const PrimaryInput> 
  FindInput(const std::string& name) const {
    OptionalRef<const PrimaryInput> ret;
    if (auto search = inputs_.find(name); search != inputs_.end()) {
      ret = *search->second;
    }
    return ret;
  }
  
  inline OptionalRef<const PrimaryInput> FindInput(const z3::expr& e) const {
    OptionalRef<const PrimaryInput> ret;
    if (auto search = expr2input_.find(e); search != expr2input_.end()) {
      ret = search->second;
    }
    return ret;
  }

  size_t num_vars() const { return vars_.size(); }
  size_t num_inputs() const { return inputs_.size(); }


  // L or W
  bool IsControlLocation(const z3::expr& e) const;

  // L
  bool IsLocation(const z3::expr& e) const;


  inline z3::context& ctx() const { return ctx_; }



  // Using the system ==========================================================

  /// Will be called before sending to the Checker (Checker has const reference)
  virtual void Prepare();

  // the following should be override when you're making a subclass
  // you should make a subclass for any new format of transition system

  /*!
   * constraints that ensure all preds of a node are one-hot
   */
  virtual void AddOneHots(Solver&) const;

  /*!
   * T constraints, basically. why does this exist again?
   */
  virtual void AddStateUpdates(Solver&) const = 0;

  /*!
   * Adds initial state to the solver
   */
  virtual void AddInitialStateToChecker(Solver&) const = 0;

  /*!
   * Adds T to the solver. Called right before search begins, one time.
   */
  virtual void AddTransitionsToChecker(Solver&) const = 0;

  /**
   * z - expanded preimage in terms of current state vars only
   * sSliceT - s in terms of next state vars and enough of T for feasibilyt checking
   */
  virtual std::shared_ptr<AbstractModel>
  ExpandedPreimage(CheckerSat& CS, const std::shared_ptr<Model>& m, const Cube& s, Cube& pre,
                   std::shared_ptr<TSlice> *sSliceT) const = 0;

  virtual void SimplifyPreimage(Cube& z) const;


  //! Must return the solver logic in z3 to use
  virtual const char *solver_logic() const = 0;

  virtual std::shared_ptr<AbstractModel> GetModel(const std::shared_ptr<Model>&) const;

  /**
   * Returns the same sol_expression with all state variables substituted with next
   * state versions. Walks the entire sol_expression, so, don't call it more than
   * you have to.
   */
  z3::expr prime(const z3::expr& e) const;

  z3::expr unprime(const z3::expr& e) const;

  virtual std::ostream& Print(std::ostream& os) const;


  //! checks if formula is a formula over T(X, Y, X+), possibly including
  //! uninterpreted constants
  bool is_trans_formula(const z3::expr&) const;

  void collect_static_statistics(Statistics *st) const;

  //^--------------------------------------------------------------------------^

  class ConstVarIterator 
      : public boost::iterator_facade<ConstVarIterator,
                                      const StateVar,
                                      boost::bidirectional_traversal_tag> {
   public:
    ConstVarIterator() = default;
    ConstVarIterator(
        VarMap<std::shared_ptr<StateVar>>::const_iterator start) 
        : it_(start) {}
   
   private:
    friend class boost::iterator_core_access;

    void increment() { ++it_; }
    void decrement() { --it_; }

    bool equal(const ConstVarIterator& other) const {
      return it_ == other.it_;
    }

    const StateVar& dereference() const { return *it_->second; }

    VarMap<std::shared_ptr<StateVar>>::const_iterator it_;
  };

  //^--------------------------------------------------------------------------^

  class ConstInputIterator 
      : public boost::iterator_facade<ConstInputIterator,
                                      const PrimaryInput,
                                      boost::bidirectional_traversal_tag> {
   public:
    ConstInputIterator() = default;
    ConstInputIterator(
        VarMap<std::shared_ptr<PrimaryInput>>::const_iterator start) 
        : it_(start) {}
   
   private:
    friend class boost::iterator_core_access;

    void increment() { ++it_; }

    bool equal(const ConstInputIterator& other) const {
      return it_ == other.it_;
    }

    const PrimaryInput& dereference() const { return *it_->second; }

    VarMap<std::shared_ptr<PrimaryInput>>::const_iterator it_;
  };
  
  //^--------------------------------------------------------------------------^
  
  inline ConstVarIterator vbegin() const {
    return ConstVarIterator(std::begin(vars_));
  }
  inline ConstVarIterator vend() const {
    return ConstVarIterator(std::end(vars_));
  }

  auto vars() const {
    return boost::make_iterator_range(vbegin(), vend());
  }

  inline ConstInputIterator ibegin() const {
    return ConstInputIterator(std::begin(inputs_));
  }
  inline ConstInputIterator iend() const {
    return ConstInputIterator(std::end(inputs_));
  }
  
  auto inputs() const {
    return boost::make_iterator_range(ibegin(), iend());
  }

  class Stats;

 protected:
  explicit TransitionSystem(z3::context& cxt);
  TransitionSystem(const TransitionSystem&);
  TransitionSystem(TransitionSystem&&);
 
  /** Initial state. */
  z3::expr init_state_;
  /** Property.  */
  z3::expr property_;

  bool vars_changed_ = true;

  // master primary input list
  VarMap<std::shared_ptr<PrimaryInput>> inputs_;
  // maps input expr to obj
  ExprMap<PrimaryInputRef> expr2input_;
  // master state var list
  VarMap<std::shared_ptr<StateVar>> vars_;
  // mapss currs_ and nexts_ to state var
  ExprMap<StateVarRef> expr2var_;

  // used to define the substitution in next() and curr()
  std::unique_ptr<CachingExprSubstitution> prime_;
  std::unique_ptr<CachingExprSubstitution> unprime_;

  /// control representation
  IpRepr ip_;

 private:
  z3::context& ctx_;
  z3::params simplify_params_;
};




inline std::ostream& operator<<(std::ostream& os, const TransitionSystem& ts) {
  return ts.Print(os);
}

}

void mylog(const euforia::uninterpreted_partition& up);



#endif /* defined(__euforia__transition_system__) */
