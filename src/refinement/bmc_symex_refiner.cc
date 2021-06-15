// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "refinement/bmc_symex_refiner.h"

#include <boost/algorithm/cxx11/any_of.hpp>
#include <boost/range/algorithm/for_each.hpp>
#include <boost/range/algorithm/copy.hpp>
#include <boost/range/algorithm/transform.hpp>
#include <boost/variant.hpp>

#include "abstract_checker_impl.h"
#include "checker.h"
#include "counterexample.h"
#include "existential_elimination.h"
#include "refinement/layered_refinement.h"
#include "refinement/symex.h"
#include "supp/boolector_evaluator.h"
#include "supp/boolector_solver.h"
#include "supp/euforia_config.h"
#include "supp/expr_iterators.h"
#include "supp/expr_set_traversal.h"
#include "supp/expr_stats.h"
#include "supp/expr_substitution.h"
#include "supp/expr_supp.h"
#include "supp/marco.h"
#include "supp/model_justifier.h"
#include "supp/reachability_graph.h"
#include "supp/std_supp.h"
#include "supp/z3_solver.h"
#include "tslice.h"
#include "xsys/abstract_vmt_transition_system.h"
#include "xsys/primary_inputs.h"
#include "xsys/state_vars.h"
#include "xsys/var_info_traversal.h"


namespace {
using namespace euforia;

template <typename OutputIt>
static void FindSymexVars(const TransitionSystem& cts,
                           const z3::expr& e, OutputIt it_out) {
  auto is_symex_name = [&](const z3::expr& e) { 
    return e.num_args() == 0 && !IsValue(e) && !cts.FindVar(e) &&
        !cts.FindInput(e);
  };
  copy_if(po_expr_iterator::begin(e), po_expr_iterator::end(e), it_out,
          is_symex_name);
}

} // end namespace


namespace euforia {

using CoreOrNewState = BmcSymexRefiner::CoreOrNewState;
  
BmcSymexRefiner::BmcSymexRefiner(
    AbstractChecker::Impl& achk, std::shared_ptr<Solver> s, int64_t nr)
    : Refiner(achk, s, nr), stats_({}) {}


CoreOrNewState BmcSymexRefiner::operator()(
    const ReachStep& step,
    const shared_ptr<symex::State>& state) {
  logger.Log(4, "**** state cx[{}] ****", step.state_index());
  logger.Log(4, "{{{{{{\n{}}}}}}}", *state);
  logger.Log(3, "on inputs In[{}], transition T, must step to state A[{}]+",
             step.input_index(), step.next_state_index());
  CoreOrNewState ret = Query(state, step);
  if (ExprSet *core = boost::get<ExprSet>(&ret)) {
    // XXX call this to record stats or something
    // CharacterizeMus(AndExprSet(axsys_.ctx(), *ret));
    const ConcreteVmtTransitionSystem& cxsys = axsys_.cts();
    // When we get a core during BMC, it means, as usual, EUForia needs to
    // learn a lemma. However, cores produced during BMC may contain
    // undesirable variables. This code collects those variables in
    // vars_to_remove. If there are such variables, we add the concrete
    // assignments from the state and re-do the query -- giving us a possibly
    // modified MUS. The query should be unsat, because we all that's done is
    // to add constraints to the query. But since the assignment is in there,
    // variable elimination will be able to remove everything in vars_to
    // remove, possibly at the cost of learning something not very general.
    ExprSet vars_to_remove;
    for (auto& lit : *core) {
      FindSymexVars(cxsys, lit, 
                    inserter(vars_to_remove, vars_to_remove.end()));
    }
    if (!vars_to_remove.empty()) {
      ++stats_.num_mus_with_bad_vars;
      // If there are vars to remove then we take the simple way out. We just
      // use the assignment in the pre-state to eliminate *all* the variables
      // there.
      logger.Log(4, "using pre-state to 'generalize' mus");
      z3::expr prev_assignment(cxsys.ctx());
      ExprAndInserter prev_ass_inserter(prev_assignment);
      auto pre_step_model = state->pre_step_model();
      for (const auto& v : cxsys.vars()) {
        auto assignment = pre_step_model->assignment(v.next());
        auto constraint = assignment->as_constraint(v.current());
        for (auto&& f : ExprConjuncts(constraint)) {
          *prev_ass_inserter++ = f;
        }
      }
      // for (auto&& [name, ass] : state->one_step_pre_assignment()) {
      //   const auto& var = cxsys.FindVar(name);
      //   // XXX when the assignment is to an array, this makes it a huge nested
      //   // store. the MUS of the one step query below could remove elements of
      //   // the prev state if instead of stores they were selects. this can be
      //   // done easily since they will all be disjoint.
      //   // XXX this is wrong because it constraints current == store(current) wtf dude
      //   for (auto&& conjunct : ExprConjuncts(ass->AsConstraint(var->current()))) {
      //     *prev_ass_inserter++ = conjunct;
      //   }
      // }

      auto prev_state_elimd = state->executor().InitState(
          ExprSet({prev_assignment}));

      // perform the query that gave us the mus again, expecting it to be unsat,
      // but with something we can directly use
      ret = Query(prev_state_elimd, step);
      if (ExprSet *core2 = boost::get<ExprSet>(&ret); !core2) {
        assert("eliminated mus query was sat, should be unsat");
        // XXX the MUS here may contain a bunch of nested logic from the transition
        // relation. using interpolants instead of MUSes would fix this.
        // XXX perhaps use a tseitin encoding with unsat cores would help this
      }
    }
  }
  return ret;
}

CoreOrNewState BmcSymexRefiner::Query(
    const shared_ptr<symex::State>& state, const ReachStep& step) {
  auto format_step = [&]() {
    return fmt::format("cx[{}] & In[{}] & T & A[{}]+",
                       step.state_index(), step.input_index(),
                       step.next_state_index());
  };

  boost::variant<ExprSet, shared_ptr<symex::State>> ret;
  auto concretize = [&](auto&& e) {
    return axsys_.Concretize(e);
  };
  ExprSet trans_hat;
  boost::copy(ExprConjuncts(axsys_.trans()),
              std::inserter(trans_hat, trans_hat.end()));
  vector<z3::expr> assumptions;
  auto& i_hat = step.input();
  auto& tslice_j = step.state_transition();
  auto& s_next_hat = tslice_j.target_constraints;

  boost::copy(state->constraints(), back_inserter(assumptions));
  boost::transform(i_hat, back_inserter(assumptions), concretize);
  boost::transform(trans_hat, back_inserter(assumptions), concretize);
  boost::transform(s_next_hat, back_inserter(assumptions), concretize);
  if (!LOG_DIR.empty()) {
    auto benchmark_name = fmt::format("{}/ref1-fwdimage{}.smt2", LOG_DIR,
                                      num_refinements_+1,
                                      step.state_index());
    ofstream outfile(benchmark_name);
    solver().DumpBenchmark(outfile, assumptions);
    logger.Log(3, "logging benchmark {}", benchmark_name);
  }
  TimerDuration d(0);
  ScopedTimeKeeper query_time(&d);
  BTOR_LOG_UP(kBtorLogLevel);
  auto feasible = solver().Check(assumptions) == CheckResult::kSat;
  BTOR_LOG_DOWN();
  auto duration = query_time.get();
  if (!feasible) {
    // query was UNSAT
    logger.Log(3, "{} is CUNSAT [{} s]", format_step(), duration.count());
    auto core = solver().unsat_core();
    ret = ExprSet(core.begin(), core.end());
  } else {
    // query was SAT
    auto model = state->executor().get_model();
    auto eval = [&](const z3::expr& e, bool) { return model->Eval(e); };
    ModelJustifier justify(eval);
    logger.Log(3, "{} is CSAT [{} s]",
               format_step(), duration.count());
    logger.LogOpenFold(3, "simulating next state");
    logger.LogOpenFold(4, "assignments of satisfiable step");
    logger.Log(4, "{}", *model);
    logger.LogCloseFold(4, "");
    auto symbolic_next = make_shared<symex::State>(state);
    ExprSet inputs, trans, s_next;
    logger.LogOpenFold(4, "input constraints:");
    boost::transform(i_hat, inserter(inputs, inputs.begin()), concretize);
    logger.Log(4, "{}", inputs);
    logger.LogCloseFold(4, "");
    logger.LogOpenFold(4, "s_next constraints:");
    boost::transform(
        s_next_hat, inserter(s_next, s_next.begin()), concretize);
    logger.Log(4, "{}", s_next);
    logger.LogCloseFold(4, "");
    justify.ComputePredicates(axsys_.cts().trans(), &trans);
    symbolic_next->Simulate(inputs, trans, s_next);
    symbolic_next->set_pre_step_model(model);
    ret = symbolic_next;
    logger.LogCloseFold(3, "next state simulated");
  }
  return ret;
}
  
void BmcSymexRefiner::ValidateLemma(
    const ReachStep& step, const shared_ptr<symex::State>& state,
    const AbstractLemmaClause& lemma) {
  assert(is_literal_false(step.step_model().Eval(lemma.as_expr())));
  z3::expr transition(axsys_.ctx());
  boost::copy(state->constraints(), ExprAndInserter(transition));
  boost::copy(step.input(), ExprAndInserter(transition));
  boost::copy(step.state_transition().transition_constraints,
              ExprAndInserter(transition));
  boost::copy(step.state_transition().target_constraints,
              ExprAndInserter(transition));
  achk_.ValidateLemma(lemma, transition);
}

void BmcSymexRefiner::collect_statistics(Statistics *st) const {
  st->Update("symex-bmc num mus with bad vars", stats_.num_mus_with_bad_vars);
}

} // end namespace euforia
