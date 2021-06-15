// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef abstract_checker_hpp
#define abstract_checker_hpp

#include <vector>
#include <propagate_const.h>
#include <memory>

#include "supp/statistics.h"

namespace z3 {
class expr;
}

namespace euforia {
class Checker;
class Counterexample;
struct BoolectorCounterexample;

namespace vmt {
class ConcreteVmtTransitionSystem;
class AbstractVmtTransitionSystem;
}

class AbstractChecker {
 public:
  struct Stats {
    int64_t num_cx = 0;
    int64_t num_refinements = 0;
  };

  AbstractChecker(vmt::AbstractVmtTransitionSystem&);
  ~AbstractChecker();
  
  /// returns true - found concrete Counterexample
  /// returns fals - property holds
  bool Run();
  
  // If run() returned true, this retrieves the concrete Counterexample
  std::unique_ptr<Counterexample> TakeCounterexample();
  
  void checkConcretizedInvariant();

  std::vector<z3::expr> MinimizeConcretizedInvariant() const;

  std::vector<z3::expr> InductiveInvariant() const;
  
  std::vector<z3::expr> concrete_invariant_query() const;

  void set_abstraction_refinement(bool b) { abstraction_refinement_ = b; }

  void collect_statistics(Statistics *st) const;

  class Impl;
 private:
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;
  Stats stats_;
  
  const vmt::ConcreteVmtTransitionSystem& cxsys_;
  vmt::AbstractVmtTransitionSystem& axsys_;
  std::unique_ptr<Checker> achk_;

  bool abstraction_refinement_;
  
  // concrete Counterexample
  std::unique_ptr<Counterexample> concrete_cx_;
};

}

#endif /* abstract_checker_hpp */
