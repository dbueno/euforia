// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_BMC_REFINER_H_
#define EUFORIA_BMC_REFINER_H_

#include "abstract_checker_impl.h"
#include "refinement/refiner.h"
#include "supp/statistics.h"

namespace euforia {

class BmcSymexRefiner : public Refiner {
 public:
  struct Stats {
    int64_t num_mus_with_bad_vars;
  };

  BmcSymexRefiner(AbstractChecker::Impl& achk,
                  std::shared_ptr<Solver> s, int64_t nr);

  // Represents either an unsat core from an UNSAT query, or a
  // newly-constructed symbolic state from a SAT query
  using CoreOrNewState = boost::variant<ExprSet, shared_ptr<symex::State>>;


  //! \param i - index into concrete cx
  CoreOrNewState operator()(
      const ReachStep& step, const shared_ptr<symex::State>& state);

  void ValidateLemma(
      const ReachStep& step, const shared_ptr<symex::State>& state,
      const AbstractLemmaClause& lemma);

  void collect_statistics(Statistics *st) const;

 private:
  Stats stats_;

  CoreOrNewState Query(const shared_ptr<symex::State>& state,
                       const ReachStep& step);
};

} // end namespace euforia

#endif
