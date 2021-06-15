// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_STEP_REFINER_H_
#define EUFORIA_STEP_REFINER_H_

#include "abstract_checker_impl.h"
#include "refiner.h"

namespace euforia {

//! The main purpose of this class is to factor out the refinement computation
//! from the Solver and from when the refinement computation occurs.
class StepRefiner : public Refiner {
 public:
  StepRefiner(AbstractChecker::Impl& achk,
              const std::shared_ptr<Solver>& s, const ReachStep& step,
              int64_t nr)
      : Refiner(achk, s, nr), step_(step) {}

  //! Checks feasibility of T & (z - i -> s+). Returns either an unsat core if
  //! step is infeasible, or nothing if it is feasible
  boost::optional<ExprSet> operator()();

  void ValidateLemma(const AbstractLemmaClause& lemma);

  void set_uniq(const std::string& s) { uniq_ = s; }

 private:
  std::string uniq_;
  const ReachStep& step_;
};

//^----------------------------------------------------------------------------^

class StepRefinerWithoutT : public Refiner {
 public:
  StepRefinerWithoutT(AbstractChecker::Impl& achk,
                      const std::shared_ptr<Solver>& s,
                      const ReachStep& step, int64_t nr)
      : Refiner(achk, s, nr), step_(step) {}

  boost::optional<ExprSet> operator()();
  
  void ValidateLemma(const AbstractLemmaClause& lemma);

 private:
  const ReachStep& step_;
};

} // end namespace euforia

#endif
