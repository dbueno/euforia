// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_XSYS_ABSTRACT_VMT_TRANSITION_SYSTEM_H_
#define EUFORIA_XSYS_ABSTRACT_VMT_TRANSITION_SYSTEM_H_

#include <memory>
#include <propagate_const.h>

#include "abstraction_manager.h"
#include "xsys/concrete_vmt_transition_system.h"


namespace euforia {
namespace config {
struct Config;
}
class Statistics;

namespace vmt {

class AbstractVmtTransitionSystem : public VmtTransitionSystem {
 public:
  AbstractVmtTransitionSystem(ConcreteVmtTransitionSystem& cts,
                              const config::Config& c);
  ~AbstractVmtTransitionSystem();
  AbstractVmtTransitionSystem(AbstractVmtTransitionSystem&) = delete;
  AbstractVmtTransitionSystem& operator=(AbstractVmtTransitionSystem&) = delete;
  
  virtual std::ostream& Print(std::ostream& os) const override;
  
  const ConcreteVmtTransitionSystem& cts() const { return cts_; }
  ConcreteVmtTransitionSystem& cts() { return cts_; }

  //! Returns the part of the transition relation represented as equations.
  //! Note that trans() is still the real transition relation.
  virtual boost::optional<EquationMapRef> trans_equations() const override;
  //! Returns the part of the transition relation not represented as equations
  virtual z3::expr trans_rest() const override;
  
  //! Gets background assertions that constrain/inform the abstraction. For now,
  //! this contains the assertion that all abstracted constants are distinct
  //! from one another. The result may change after a refinement pass, due to
  //! introducing new uninterpreted constants (a side effect of abstracting new
  //! concrete terms with never-before-seen constants).
  z3::expr get_abstract_background() const;
  
  // overrides
  using VmtTransitionSystem::Prepare;

  virtual void AddInitialStateToChecker(Solver&) const override;
  virtual void AddTransitionsToChecker(Solver&) const override;
  virtual void AddOneHots(Solver&) const override;

  void AddDistinctConstConstraint(Solver&) const;

  ExprSet::const_iterator constants_begin() const {
    return absman_->constants().begin();
  }
  
  ExprSet::const_iterator constants_end() const {
    return absman_->constants().end();
  }

  virtual std::shared_ptr<AbstractModel>
  GetModel(const std::shared_ptr<Model>&) const override;

  // z out - will contain the preimage Cube in terms of present state variables
  // sSliceT out - will contain s in terms of next state vars and enough of T to make feasibilyt chekcing a snap
  std::shared_ptr<AbstractModel> 
  ExpandedPreimage(CheckerSat& CS, const std::shared_ptr<Model>& model, const Cube& s, Cube& z,
                   std::shared_ptr<TSlice> *sSliceT) const override;

  virtual void SimplifyPreimage(Cube& z) const override;

  const char *solver_logic() const override;

  //! Abstract the given concrete expression. May change the abstraction
  //! manager and introduce new constants, changing @get_abstract_background().
  z3::expr Abstract(const z3::expr& e) const;

  /// Concretize an abstract expression
  z3::expr Concretize(const z3::expr& lit) const;

  /// Get current set of abstract constants used
  const ExprSet& constants() const;

  void PrintStats(std::ostream&) const;
  void collect_statistics(Statistics *st) const;

  struct Stats;
  void collect_static_statistics(Statistics *st) const;

 private:
  ConcreteVmtTransitionSystem& cts_;
  std::unique_ptr<AbstractionManager> absman_;
  std::unique_ptr<Stats> stats_;
  class Impl;
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;

  // garbage
  const bool eager_constant_ordering_ = false;
};
} // namespace vmt
} // namespace euforia

#endif /* EUFORIA_XSYS_ABSTRACT_VMT_TRANSITION_SYSTEM_H_ */
