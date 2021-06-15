// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "step_refiner.h"

#include <boost/algorithm/cxx11/any_of.hpp>

#include "checkersat.h"
#include "supp/reachability_graph.h"
#include "tslice.h"

namespace euforia {

//! Checks feasibility of T & (z - i -> s+). Returns either an unsat core if
//! step is infeasible, or nothing if it is feasible
boost::optional<ExprSet> StepRefiner::operator()() {
  auto model_falsifies = [&](auto&& lemma) {
    return is_literal_false(step_.step_model().Eval(lemma->as_expr()));
  };
  if (boost::algorithm::any_of(achk_.recent_lemmas(), model_falsifies)) {
    logger.Log(3,
               "skipping refining step {} because model falsifies lemma",
               step_.next_state_index());
    return boost::none;
  }

  boost::optional<ExprSet> ret;
  vector<z3::expr> assumptions;

  auto Concretize = [&](auto&& e) {
    return axsys_.Concretize(e);
  };
  auto& z_hat = step_.state();
  transform(z_hat.begin(), z_hat.end(), back_inserter(assumptions),
            Concretize);
  auto& i_hat = step_.input();
  transform(i_hat.begin(), i_hat.end(), back_inserter(assumptions),
            Concretize);
  auto& s_next_hat = step_.state_transition().target_constraints;
  transform(s_next_hat.begin(), s_next_hat.end(), back_inserter(assumptions),
            Concretize);
  // T -- projected by model
  auto& transition_model = step_.step_model();
  copy_trans_predicates(transition_model, back_inserter(assumptions));
  if (!LOG_DIR.empty()) {
    auto benchmark_name = fmt::format(
        "{}/ref{}-step{}-{}.{}.smt2", LOG_DIR, num_refinements_+1,
        step_.state_index(), step_.next_state_index(),
        solver_->version());
    ofstream outfile(benchmark_name);
    fmt::print(outfile, "; {} input constraints\n", i_hat.size());
    fmt::print(outfile, "; {} target constraints\n", s_next_hat.size());
    fmt::print(outfile, "; {} assumptions\n", assumptions.size());
    // fmt::print(outfile, "; {} trans constraints\n", num_trans_predicates);
    solver().DumpBenchmark(outfile, assumptions);
    logger.Log(3, "logging benchmark {}", benchmark_name);
  }
  stats() = CalculateStats(assumptions);
  TimerDuration d(0); {
    ScopedTimeKeeper step_time(&d);
    BTOR_LOG_UP(kBtorLogLevel);
    auto feasible = solver().Check(assumptions) == CheckResult::kSat;
    BTOR_LOG_DOWN();
    auto diff = step_time.Get();
    if (!feasible) {
      logger.Log(3, "A[{}] & In[{}] & T & A[{}]+ is CUNSAT [{} s]",
                 step_.state_index(), step_.input_index(), step_.next_state_index(),
                 diff.count());
      auto core = solver().unsat_core();
      ret = ExprSet(core.begin(), core.end());
    } else {
      logger.Log(3, "A[{}] & In[{}] & T & A[{}]+ is CSAT [{} s]", 
                 step_.state_index(), step_.input_index(), step_.next_state_index(),
                 diff.count());
    }
  }
  return ret;
}
  
void StepRefiner::ValidateLemma(const AbstractLemmaClause& lemma) {
  assert(is_literal_false(step_.step_model().Eval(lemma.as_expr())));
  z3::expr transition(axsys_.ctx());
  boost::copy(step_.state(), ExprAndInserter(transition));
  boost::copy(step_.input(), ExprAndInserter(transition));
  boost::copy(step_.state_transition().target_constraints,
              ExprAndInserter(transition));
  copy_trans_predicates(step_.step_model(), ExprAndInserter(transition));
  achk_.ValidateLemma(lemma, transition);
}

//^----------------------------------------------------------------------------^

boost::optional<ExprSet> StepRefinerWithoutT::operator()() {
  boost::optional<ExprSet> ret;
  vector<z3::expr> assumptions;

  auto Concretize = [&](auto&& e) {
    return axsys_.Concretize(e);
  };
  auto& z_hat = step_.state();
  transform(z_hat.begin(), z_hat.end(), back_inserter(assumptions),
            Concretize);
  auto& i_hat = step_.input();
  transform(i_hat.begin(), i_hat.end(), back_inserter(assumptions),
            Concretize);
  auto& s_next_hat = step_.state_transition().target_constraints;
  transform(s_next_hat.begin(), s_next_hat.end(), back_inserter(assumptions),
            Concretize);

  if (!LOG_DIR.empty()) {
    auto benchmark_name = fmt::format("{}/ref{}-step{}-{}-without-t.smt2",
                                      LOG_DIR, num_refinements_+1,
                                      step_.state_index(),
                                      step_.next_state_index());
    ofstream outfile(benchmark_name);
    fmt::print(outfile, "; {} input constraints\n", i_hat.size());
    fmt::print(outfile, "; {} target constraints\n", s_next_hat.size());
    fmt::print(outfile, "; {} assumptions\n", assumptions.size());
    // fmt::print(outfile, "; {} trans constraints\n", num_trans_predicates);
    solver().DumpBenchmark(outfile, assumptions);
    logger.Log(3, "logging benchmark {}", benchmark_name);
  }
  stats() = CalculateStats(assumptions);
  TimerDuration d(0);
  ScopedTimeKeeper step_time(&d);
  BTOR_LOG_UP(kBtorLogLevel);
  auto feasible = solver().Check(assumptions) == CheckResult::kSat;
  BTOR_LOG_DOWN();
  auto diff = step_time.Get();
  if (!feasible) {
    logger.Log(3, "A[{}] & In[{}] & A[{}]+ is CUNSAT [{} s]", 
               step_.state_index(), step_.input_index(),
               step_.next_state_index(), diff.count());
    auto core = solver().unsat_core();
    ret = ExprSet(core.begin(), core.end());
  } else {
    logger.Log(3, "A[{}] & In[{}] & A[{}]+ is CSAT [{} s]",
               step_.state_index(), step_.input_index(),
               step_.next_state_index(), diff.count());
    // XXX make the next state? return that?
  }
  return ret;
}
  
void StepRefinerWithoutT::ValidateLemma(const AbstractLemmaClause& lemma) {
  assert(is_literal_false(step_.step_model().Eval(lemma.as_expr())));
  z3::expr transition(axsys_.ctx());
  boost::copy(step_.state(), ExprAndInserter(transition));
  boost::copy(step_.input(), ExprAndInserter(transition));
  boost::copy(step_.state_transition().target_constraints,
              ExprAndInserter(transition));
  achk_.ValidateLemma(lemma, transition);
}
} // end namespace euforia
