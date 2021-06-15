// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_XSYS_VMT_TRANSITION_SYSTEM_H_
#define EUFORIA_XSYS_VMT_TRANSITION_SYSTEM_H_

#include <propagate_const.h>
#include <unordered_map>
#include <vector>

#include "xsys/transition_system.h"

namespace euforia {
namespace vmt {
struct MathsatVmtAst;

class VmtTransitionSystem  : public TransitionSystem {
 public:
  VmtTransitionSystem(MathsatVmtAst& ast, z3::context&);
  explicit VmtTransitionSystem(z3::context&);
  VmtTransitionSystem(const VmtTransitionSystem&);
  VmtTransitionSystem(VmtTransitionSystem&&);
  ~VmtTransitionSystem();
 
  // constraints that ensure all preds of a node are one-hot
  virtual const char *solver_logic() const override;
  virtual void AddOneHots(Solver&) const override;
  virtual void AddStateUpdates(Solver&) const override;
  virtual void AddInitialStateToChecker(Solver&) const override;
  virtual void AddTransitionsToChecker(Solver&) const override;
  virtual std::shared_ptr<AbstractModel>
  ExpandedPreimage(CheckerSat& CS, const std::shared_ptr<Model>& m, const Cube& s, Cube& pre,
                   std::shared_ptr<TSlice> *sSliceT) const override;
  
  void RewriteSystem(const std::function<z3::expr(const z3::expr&)>& rewrite);
    
  virtual std::ostream& Print(std::ostream& os) const override;

  virtual inline z3::expr trans() const override {
    return trans_;
  }

  //! Get background assertion, if any. Returns true if the VMT file did not
  //! specify any background assertions.
  z3::expr background() const {
    if (bool(background_)) {
      return background_;
    } else {
      return background_.ctx().bool_val(true);
    }
  }

  void set_trans(const z3::expr& t) {
    trans_ = t;
  }

#if UNUSED_PART_OF_OLD_TSEITIN_GARBAGE
  inline const std::vector<z3::expr> trans_clauses() const {
    return trans_clauses_;
  }
#endif
 
  struct Stats;
  void collect_static_statistics(Statistics *st) const;

 protected:
  z3::expr trans_;       // stands alone
  std::vector<z3::expr> trans_clauses_;
  z3::expr background_; // possibly null

 private:
  class Impl;
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;
};
}
}

#endif
