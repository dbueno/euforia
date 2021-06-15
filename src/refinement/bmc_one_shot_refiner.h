// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_BMC_ONE_SHOT_REFINER_H_
#define EUFORIA_BMC_ONE_SHOT_REFINER_H_

#include <memory>

#include "abstract_checker_impl.h"
#include "counterexample.h"
#include "refiner.h"

namespace euforia {

class BmcStep {
 public:
  BmcStep(z3::context& c, int index) 
      : subst_(c), current_vars_(c), state_index_(index) {}

  bool has_transition() const {
    assert(bool(input_vars_) == bool(next_vars_));
    return bool(next_vars_);
  }

  const z3::expr_vector& current_vars() const { return current_vars_; }
  const z3::expr_vector& next_vars() const { return *next_vars_; }
  const z3::expr_vector& input_vars() const { return *input_vars_; }

  const auto& constraints() const { return constraints_; }

  const ExprSubstitution& subst() const { return subst_; }

  int state_index() const { return state_index_; }
  int input_index() const {
    assert(has_transition());
    return state_index_+1;
  }
  int next_state_index() const {
    assert(has_transition());
    return state_index_+1;
  }

 private:
  friend class BmcOneShotRefiner;

  ExprSet constraints_;
  // Substitution from (X, Y, X') to vars with step numbers
  ExprSubstitution subst_;
  z3::expr_vector current_vars_;
  boost::optional<z3::expr_vector> input_vars_;
  boost::optional<z3::expr_vector> next_vars_;
  int state_index_;

  auto constraint_inserter() {
    return std::inserter(constraints_, constraints_.begin());
  }
};

std::ostream& operator<<(std::ostream& os, const BmcStep&);

//^----------------------------------------------------------------------------^

class BmcOneShotRefiner : public Refiner {
 public:
  BmcOneShotRefiner(AbstractChecker::Impl& achk,
                    const std::shared_ptr<Solver>& s,
                    const ReachabilityGraph& acx, int64_t nr);
  ~BmcOneShotRefiner();

  // Returns a list of cores or nothing, if SAT
  boost::optional<z3::expr_vector> operator()();

  std::unique_ptr<Counterexample> make_counterexample();

  void ValidateLemma(const AbstractLemmaClause& lemma);

  class Impl;
 private:
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;
};

} // end namespace euforia

#endif
