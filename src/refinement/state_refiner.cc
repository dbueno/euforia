// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "state_refiner.h"

#include <boost/algorithm/cxx11/any_of.hpp>

#include "checkersat.h"
#include "supp/reachability_graph.h"

namespace euforia {
  
boost::optional<ExprSet> StateRefiner::operator()(int n) {
  auto model_falsifies = [&](auto&& lemma) {
    return is_literal_false(step_.step_model().Eval(lemma->as_expr()));
  };
  if (step_.has_transition() &&
      boost::algorithm::any_of(achk_.recent_lemmas(), model_falsifies)) {
    logger.Log(3,
               "skipping refining state {} because model falsifies lemma",
               n);
    return boost::none;
  }

  boost::optional<ExprSet> ret;
  vector<z3::expr> assumptions;
  auto Concretize = [&](auto&& e) {
    return axsys_.Concretize(e);
  };

  auto &s_hat = step_.state();
  transform(s_hat.begin(), s_hat.end(), back_inserter(assumptions),
            Concretize);
  if (!LOG_DIR.empty()) {
    auto benchmark_name = fmt::format(
        "{}/ref{}-state{}.{}.smt2", LOG_DIR, num_refinements_+1, n,
        solver_->version());
    ofstream outfile(benchmark_name);
    solver().DumpBenchmark(outfile, assumptions);
    logger.Log(3, "logging benchmark {}", benchmark_name);
  }
  stats() = CalculateStats(assumptions);
  TimerDuration d(0);
  ScopedTimeKeeper state_time(&d);
  BTOR_LOG_UP(kBtorLogLevel);
  auto feasible = solver().Check(assumptions) == CheckResult::kSat;
  BTOR_LOG_DOWN();
  auto diff = state_time.Get();
  if (!feasible) {
    logger.Log(3, "A[{}] is CUNSAT [individual eavg: {:.3f} s]", n,
               diff.count());
    auto core = solver().unsat_core();
    ret = ExprSet(core.begin(), core.end());
  } else {
    logger.Log(3, "A[{}] is CSAT [individual eavg: {:.3f} s]", n,
               diff.count());
  }
  return ret;
}
  

void StateRefiner::ValidateLemma(const AbstractLemmaClause& lemma) {
  assert(is_literal_false(step_.step_model().Eval(lemma.as_expr())));
  z3::expr acx_formula(achk_.ctx());
  boost::copy(step_.state(), ExprAndInserter(acx_formula));
  achk_.ValidateLemma(lemma, acx_formula);
}

} // end namespace euforia
