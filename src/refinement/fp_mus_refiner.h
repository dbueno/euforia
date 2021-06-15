// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_FP_REFINER_H_
#define EUFORIA_FP_REFINER_H_

#include <boost/iterator/iterator_facade.hpp>
#include <memory>

#include "abstract_checker_impl.h"
#include "counterexample.h"
#include "refiner.h"
#include "bmc_one_shot_refiner.h"

namespace euforia {
class BmcStep;
class BmcUnsatStep;
class BmcUnsatIterator;

//! Represents an UNSAT core from a BMC query
class BmcUnsat {
 public:
  BmcUnsat(const std::vector<BmcStep>& steps, z3::expr_vector core);

  int64_t num_steps() const {
    return static_cast<int64_t>(steps_.size());
  }

  z3::context& ctx() const { return ctx_; }

  //! Returns true if the given BMC constraint is found in the core
  bool contains(const z3::expr& e) const;

  BmcUnsatIterator bmc_begin() const;
  BmcUnsatIterator bmc_end() const;

  auto size() const { return core_.size(); }

 private:
  ExprSet core_;
  std::vector<BmcUnsatStep> steps_;
  z3::context& ctx_;
};

std::ostream& operator<<(std::ostream&, const BmcUnsat&);

//^----------------------------------------------------------------------------^
//
class BmcUnsatStep {
 public:
  BmcUnsatStep(const BmcUnsat& u, const BmcStep& s);

  bool has_transition() const { return step_.has_transition(); }

  z3::expr_vector current_vars() const;
  z3::expr_vector next_vars() const;
  z3::expr_vector input_vars() const;
  
  z3::expr core_constraints() const;

  ExprSubstitution subst() const;

  int state_index() const { return step_.state_index(); }

 private:
  const BmcUnsat& core_;
  BmcStep step_;
};

std::ostream& operator<<(std::ostream& out, const BmcUnsatStep& step);

//^----------------------------------------------------------------------------^
//
class BmcUnsatIterator
    : public boost::iterator_facade<BmcUnsatIterator,
                                    const BmcUnsatStep,
                                    boost::bidirectional_traversal_tag> {
 public:
  BmcUnsatIterator() = default;
  BmcUnsatIterator(std::vector<BmcUnsatStep>::const_iterator it) : it_(it) {}

 private:
  friend class boost::iterator_core_access;

  void increment() { ++it_; }
  void decrement() { --it_; }

  bool equal(const BmcUnsatIterator& other) const {
    return it_ == other.it_;
  }

  const BmcUnsatStep& dereference() const { return *it_; }

  std::vector<BmcUnsatStep>::const_iterator it_;
};

//^----------------------------------------------------------------------------^

// x - vector of state vars
// in each rule, inputs are quantified as well as x
// true => p0(x)
// p0(x) & (conjunction of constraints from step 0-1 that are in the MUS) => p1(x)
// p1(x) & (conjunction of constraints from step 1-2 that are in the MUS) => p2(x)
// ...
// pn(x) -> false
class FpMusRefiner : public Refiner {
 public:
  struct RuleInfo;

  using MaybeMus =
      boost::optional<ExprSet>;

  FpMusRefiner(AbstractChecker::Impl& achk,
               const std::shared_ptr<Solver>& s,
               const std::vector<BmcStep>& steps,
               z3::expr_vector core, int64_t nr);
  
  ~FpMusRefiner();

  z3::expr_vector operator()();

  void ValidateLemma(const AbstractLemmaClause& lemma);

 private:
  z3::fixedpoint fp_;
  // The vector of variables used for the interpolant predicates. It's set to
  // the concrete transition system state variables.
  // z3::expr_vector x_;
  // Corresponding sorts for x_
  // z3::sort_vector x_sorts_;
  BmcUnsat core_;
  // Maps body predicate to corresponding rule
  std::unique_ptr<FuncDeclMap<RuleInfo>> body2info_;

  z3::expr mk_init_relation();
  z3::expr RegisterRelation(int i, const BmcUnsatStep&);
  void AddRule(int i, const z3::expr& p_prev, const z3::expr& t,
               const z3::expr& p_next, const BmcUnsatStep& ustep);
  
  z3::expr_vector get_vars(int i);
  z3::expr_vector mk_rule_bound_vars(const BmcUnsatStep& step,
                               const z3::expr& p_prev,
                               const z3::expr& p_next,
                               const z3::expr& t) const;
  ExprSubstitution mk_interpolant_projection(const z3::expr& rel) const;
};

} // end namespace euforia

#endif
