// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_STATE_REFINER_H_
#define EUFORIA_STATE_REFINER_H_

#include "abstract_checker_impl.h"
#include "refiner.h"

namespace euforia {

//! The main purpose of this class is to factor out the refinement computation
//! from the Solver and from when the refinement computation occurs.
class StateRefiner : public Refiner {
 public:
  StateRefiner(AbstractChecker::Impl& achk,
               const std::shared_ptr<Solver>& s, const ReachStep& step,
               int64_t nr)
      : Refiner(achk, s, nr), step_(step) {}

  boost::optional<ExprSet> operator()(int n);

  void ValidateLemma(const AbstractLemmaClause& lemma);

 private:
  const ReachStep& step_;
};

} // end namespace euforia

#endif
