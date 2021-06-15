// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "bmc_one_shot_refiner.h"

#include <boost/range/algorithm/transform.hpp>

#include "fp_mus_refiner.h"
#include "supp/reachability_graph.h"
#include "supp/expr_substitution.h"

using namespace std;

namespace {

class CxState {
 public:
  CxState(int64_t i) : index_(i) {}

  void foo() { (void)index_; }

 private:
  int64_t index_;
};

}

//^----------------------------------------------------------------------------^

namespace euforia {

std::ostream& operator<<(std::ostream& os, const BmcStep& s) {
  fmt::print(os, "BmcStep constraints: {}\n", s.constraints());
  return os;
}

class BmcOneShotRefiner::Impl {
 public:
  Impl(BmcOneShotRefiner& parent,
       const ReachabilityGraph& reached)
      : parent_(parent), reached_(reached), vars_(ctx()),
        steps_(reached.cx_length(), BmcStep(ctx(), 0)) {
  }

  //! Returns true if feasible
  bool OneShotQuery();
  
  z3::expr_vector FindInterpolants(z3::expr_vector core);
  unique_ptr<Counterexample> mk_counterexample();

  z3::context& ctx() const { return parent_.ctx(); }
  const auto& axsys() const { return parent_.axsys(); }
  const auto& cxsys() const { return parent_.cxsys(); }
  Solver& solver() const { return *parent_.solver_; }

  bool lemma_refutes_abstract_cx(const z3::expr&);

 private:
  BmcOneShotRefiner& parent_;
  const ReachabilityGraph& reached_;
  z3::expr_vector vars_;
  // steps of the counterexample
  std::vector<BmcStep> steps_;
  std::unique_ptr<Solver> absolver_;

  ExprSubstitution MakeRenamer(int64_t i);
  ExprSubstitution mk_renamer(int64_t i) const;
  ExprSubstitution mk_input_renamer(int64_t i) const;
  ExprSubstitution mk_next_renamer(int64_t i) const;
  z3::expr get_step_var(int64_t i, const z3::expr& e) const;
};

//^----------------------------------------------------------------------------^

BmcOneShotRefiner::BmcOneShotRefiner(
    AbstractChecker::Impl& achk,
    const std::shared_ptr<Solver>& s, const ReachabilityGraph& acx,
    int64_t nr)
    : Refiner(achk, s, nr),
      pimpl_(std::make_unique<BmcOneShotRefiner::Impl>(*this, acx)) {}
  
BmcOneShotRefiner::~BmcOneShotRefiner() = default;

unique_ptr<Counterexample>
BmcOneShotRefiner::make_counterexample() {
  return pimpl_->mk_counterexample();
}

//^----------------------------------------------------------------------------^

boost::optional<z3::expr_vector>
BmcOneShotRefiner::operator()() {
  bool feasible = pimpl_->OneShotQuery();
  if (!feasible) {
    auto core = solver().unsat_core();
    return pimpl_->FindInterpolants(core);
  } else {
    return boost::none;
  }
}

//^----------------------------------------------------------------------------^

bool BmcOneShotRefiner::Impl::OneShotQuery() {
  vars_ = z3::expr_vector(ctx()); // clear
  // Creates a formula for one BMC query from the reachability graph.
  int64_t i = 1;
  for (auto it = reached_.cx_begin(), ie = reached_.cx_end(); it != ie;
       ++it, ++i) {
    const auto& reach_step = *it;
    // this loop will fill bmc_step in.
    auto& bmc_step = steps_[i-1] = {ctx(), it->state_index()};
    // Renames current state variables v to v-(i-1). Renames input variables
    // v to v-(i-1).
    const auto& subst_current = bmc_step.subst_ =
        mk_renamer(i-1);
    boost::copy(subst_current.dst(),
                ExprVectorInserter(bmc_step.current_vars_));
    const auto rename_current = [&](const z3::expr& abs_e) {
      return subst_current(axsys().Concretize(abs_e));
    };

    if (i == 1) {
      boost::transform(ExprConjuncts(cxsys().init_state()),
                       bmc_step.constraint_inserter(),
                       rename_current);
    }
    
    boost::transform(
        reach_step.state(), bmc_step.constraint_inserter(),
        rename_current);

    if (reach_step.has_transition()) {
      // Renames inputs v to v-i
      bmc_step.input_vars_ = z3::expr_vector(ctx());
      ExprSubstitution subst_input = mk_input_renamer(i);
      boost::copy(subst_input.dst(),
                  ExprVectorInserter(*bmc_step.input_vars_));
      // Renames next-state vars v to v-i.
      ExprSubstitution subst_next = mk_next_renamer(i);
      bmc_step.next_vars_ = z3::expr_vector(ctx());
      boost::copy(subst_next.dst(),
                  ExprVectorInserter(*bmc_step.next_vars_));
      bmc_step.subst_ = subst_current & subst_next & subst_input;
      auto rename_both = [&](const z3::expr& abs_e) {
        return bmc_step.subst_(axsys().Concretize(abs_e));
      };
      if (euforia_config.use_osbmc_slicing) {
        auto preds = rename_both(expr_mk_and(
            ctx(), parent_.sliced_trans_predicates(reach_step.step_model())));
        boost::copy(ExprConjuncts(preds), bmc_step.constraint_inserter());
      } else {
        auto new_trans = bmc_step.subst_(cxsys().trans());
        boost::copy(
            ExprConjuncts(new_trans), bmc_step.constraint_inserter());
      }
      
      auto inputs = rename_both(expr_mk_and(ctx(), reach_step.input()));
      boost::copy(
          ExprConjuncts(inputs), bmc_step.constraint_inserter());
    }
    logger.Log(4, "bmcstep {} constraints size: {}",
               bmc_step.state_index(), bmc_step.constraints().size());
  }

  vector<z3::expr> bmc;
  for (const auto& bmc_step : steps_) {
    logger.Log(5, "bmcstep {} constraints:\n{{{{{{{}}}}}}}",
               bmc_step.state_index(), bmc_step);
    boost::copy(bmc_step.constraints(), back_inserter(bmc));
  }
  if (!LOG_DIR.empty()) {
    auto benchmark_name = fmt::format(
        "{}/ref{}-bmc.{}.smt2", LOG_DIR, parent_.num_refinements_+1,
        parent_.solver_->version());
    ofstream outfile(benchmark_name);
    // fmt::print(outfile, "; {} input constraints\n", i_hat.size());
    // fmt::print(outfile, "; {} target constraints\n", s_next_hat.size());
    fmt::print(outfile, "; {} assumptions\n", bmc.size());
    // fmt::print(outfile, "; {} trans constraints\n", num_trans_predicates);
    solver().DumpBenchmark(outfile, bmc.size(), bmc.data());
    logger.Log(3, "logging benchmark {}", benchmark_name);
  }
  logger.Log(5, "bmc one-shot query:\n{{{{{{{}}}}}}}", bmc);
  TimerDuration d(0);
  ScopedTimeKeeper bmc_time(&d);
  auto feasible = solver().Check(bmc) == CheckResult::kSat;
  auto check_duration = bmc_time.get();
  if (!feasible) {
    logger.Log(3, "one-shot BMC is CUNSAT [{:.3f} s]",
               check_duration.count());
  } else {
    logger.Log(3, "one-shot BMC is CSAT [{:.3f} s]",
               check_duration.count());
  }
  return feasible;
}


z3::expr_vector
BmcOneShotRefiner::Impl::FindInterpolants(z3::expr_vector core) {
    FpMusRefiner get_interpolants(parent_.achk_, parent_.solver_,
                                  steps_, core,
                                  parent_.num_refinements_);
    auto cores = get_interpolants();
    // Checks that assuming the negations of all the cores refutes the abstract
    // BMC query.
    EDEBUG_CODE(
        z3::expr_vector lemmas(ctx());
        boost::transform(cores, ExprVectorInserter(lemmas), expr_not);
        assert(lemma_refutes_abstract_cx(expr_mk_and(lemmas))));
    return cores;
}


unique_ptr<Counterexample> BmcOneShotRefiner::Impl::mk_counterexample() {
  z3::expr_vector vars(ctx());
  for (const auto& bmc_step : steps_) {
    boost::copy(bmc_step.current_vars(), ExprVectorInserter(vars));
  }
  auto cx = std::make_unique<BmcOneShotCounterexample>();
  cx->set_model(solver().get_model(vars));
  // logger.Log(0, "one-shot bmc model:\n{}", *model);
  return cx;
}


ExprSubstitution BmcOneShotRefiner::Impl::mk_renamer(int64_t i) const {
  ExprSubstitution subst(ctx());
  for (const StateVar& var : cxsys().vars()) {
    auto passified_var = get_step_var(i, var.current());
    subst.AddSubstitution(var.current(), passified_var);
  }
  return subst;
}


ExprSubstitution BmcOneShotRefiner::Impl::mk_input_renamer(int64_t i) const {
  ExprSubstitution subst(ctx());
  for (const PrimaryInput& input : cxsys().inputs()) {
    auto passified_var = get_step_var(i, input);
    subst.AddSubstitution(input, passified_var);
  }
  return subst;
}


//! Renames next-state inputs with i suffix
ExprSubstitution BmcOneShotRefiner::Impl::mk_next_renamer(int64_t i) const {
  ExprSubstitution subst(ctx());
  for (const StateVar& var : cxsys().vars()) {
    auto passified_var = get_step_var(i, var.current());
    subst.AddSubstitution(var.next(), passified_var);
  }
  return subst;
}

z3::expr BmcOneShotRefiner::Impl::get_step_var(
    int64_t i, const z3::expr& e) const {
  assert(e.num_args() == 0);
  auto new_name = fmt::format("{}-{}", e.decl().name().str(), i);
  return e.ctx().constant(new_name.c_str(), e.get_sort());
}


bool
BmcOneShotRefiner::Impl::lemma_refutes_abstract_cx(const z3::expr& lemma) {
  // The lemma uses (X, Y, X'). Instantiate it for every step of the cx and
  // assert those instantiations.  Assert the bmc formula. Check for unsat.

  if (!absolver_) {
    // Initializes the solver with the abstract BMC query
    auto s = make_unique<Z3Solver>(ctx(), "QF_UF");
    z3::params p(ctx());
    p.set("model", false);
    p.set("unsat_core", false);
    s->set_params(p);
    absolver_ = move(s);
    for (auto it = steps_.begin(), ie = steps_.end(); it != ie; ++it) {
      absolver_->Add(axsys().Abstract(
              expr_mk_and(ctx(), it->constraints())));
    }
    // Sanity checks that the BMC query is abstractly feasible
    // assert(absolver_->Check() == CheckResult::kSat);
  }

  absolver_->Push();
  logger.Log(4, "lemma_refutes_abstract_cx: lemma:");
  logger.LogFold(4, "{}", axsys().Abstract(lemma));
  for (auto it = steps_.begin(), ie = steps_.end(); it != ie; ++it) {
    auto abs_lemma_bmc = axsys().Abstract(it->subst()(lemma));
    absolver_->Add(abs_lemma_bmc);
  }
  logger.Log(5, "lemma_refutes_abstract_cx: assertions:");
  logger.LogFold(5, "{}", absolver_->assertions());
  logger.Log(3, "checking that fp lemma refutes abstract cx");
  // Checks that the abstracted lemma refutes the BMC query
  auto result = absolver_->Check();
  absolver_->Pop();
  return result == CheckResult::kUnsat;
}

//^----------------------------------------------------------------------------^
} // end namespace euforia
