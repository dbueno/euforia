// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "abstract_checker_impl.h"

#include <boost/algorithm/cxx11/any_of.hpp>
#include <boost/range/algorithm/for_each.hpp>
#include <boost/range/algorithm/copy.hpp>
#include <boost/range/algorithm/transform.hpp>
#include <boost/variant.hpp>
#include <sstream>
#include <llvm/ADT/EquivalenceClasses.h>

#include "abstract_checker_impl.h"
#include "checker.h"
#include "counterexample.h"
#include "existential_elimination.h"
#include "refinement/bmc_one_shot_refiner.h"
#include "refinement/bmc_symex_refiner.h"
#include "refinement/layered_refinement.h"
#include "refinement/rmus.h"
#include "refinement/state_refiner.h"
#include "refinement/step_refiner.h"
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
#include "supp/portfolio_solver.h"
#include "supp/reachability_graph.h"
#include "supp/std_supp.h"
#include "supp/z3_solver.h"
#include "tslice.h"
#include "xsys/abstract_vmt_transition_system.h"
#include "xsys/primary_inputs.h"
#include "xsys/state_vars.h"
#include "xsys/var_info_traversal.h"

using namespace std;
using namespace boolector;
using namespace llvm;
using namespace euforia::vmt;

namespace euforia {

class Z3RefSolver : public Z3Solver {
 public:
  Z3RefSolver(z3::context& c) : Z3Solver(c) {
    // I got this configuration from ESBMC. I also found mention online
    // specifically about "solve-eqs" and about setting "relevancy" to 0 for BV
    // queries. So far, this configuration performs better than Boolector on my
    // problems.
    z3::tactic t =
        z3::tactic(ctx(), "simplify") &
        z3::tactic(ctx(), "solve-eqs") &
        z3::tactic(ctx(), "smt"); // XXX use QF_AUFBV tactic
    solver_ = t.mk_solver();
    set_params();
  }

 private:
  void set_params() {
    z3::params p(ctx());
    p.set("auto_config", true);
    p.set("relevancy", 0U);
    p.set("model", true);
    p.set("proof", false);
    p.set("unsat_core", true);
    Z3Solver::set_params(p);
  }
};
  
//^----------------------------------------------------------------------------^
//

AbstractChecker::Impl::Impl(
    const ConcreteVmtTransitionSystem& C, AbstractVmtTransitionSystem& A,
    AbstractChecker& parent)
    : cxsys_(C), axsys_(A), solver_(make_solver()),
      achk_(nullptr), parent_(parent), stats_{} {
  if (euforia_config.use_layered_refinement_queries) {
    layered_abstractor_ =
        std::make_shared<EufBvSolver::LayeredAbstraction>(C.ctx());
  }
}

AbstractChecker::Impl::~Impl() = default;

//! Makes a BoolectorSolver with settings (model generation and
//! incrementality) and assertions appropriate for refinement queries
//! (background assertion from concrete sys)
unique_ptr<BoolectorSolver> AbstractChecker::Impl::MakeBoolectorSolver() const {
  auto ret = std::make_unique<BoolectorSolver>(cxsys_.ctx());
  ret->SetOption(BTOR_OPT_MODEL_GEN, 2);
  ret->SetOption(BTOR_OPT_INCREMENTAL, 1);
  ret->AddGeneral(cxsys_.background(), true /* permanent assumption*/);
  return ret;
}

unique_ptr<Z3Solver> AbstractChecker::Impl::MakeZ3Solver() const {
  auto ret = std::make_unique<Z3RefSolver>(ctx());
  ret->Add(cxsys_.background());
  return ret;
}

unique_ptr<Solver> AbstractChecker::Impl::make_solver() const {
  unique_ptr<Solver> solver;
  switch (euforia_config.refinement_solver) {
    case config::kZ3: {
      unique_ptr<Z3Solver> s = MakeZ3Solver();
      // z3::params p(ctx());
      // p.set("auto_config", true);
      // s->set_params(p);
      solver = move(s);
      break;
    }

    case config::kBoolector: {
      solver = MakeBoolectorSolver();
      break;
    }

    default:
      EUFORIA_FATAL("no solver configured");
  }
  return solver;
}

std::unique_ptr<Counterexample>
AbstractChecker::Impl::RefineFromAcx(const ReachabilityGraph& reached) {
  const auto& num_cx = parent_.stats_.num_cx;
  logger.Log(1, "refining #{} ({} steps)", num_cx, reached.cx_length());
  logger.LogOpenFold(3, "ACX {}", num_cx);
  for (auto it = reached.cx_begin(), ie = reached.cx_end(); it != ie; ++it) {
    logger.Log(3, "ACX state A[{}] (cube {}, size {})", it->state_index(),
               it->state().ID, it->state().size());
    auto a_i = it->state().asExpr();
    for (auto &elt : ExprConjuncts(a_i)) {
      logger.Log(4, "    {}", elt);
    }
    if (it->HasTransition()) {
      logger.Log(3, "In[{}] (size {})", it->input_index(), it->input().size());
      for (auto& c : it->input()) {
        logger.Log(4, "    {}", c);
      }
      logger.Log(3, "");
    }
  }
  logger.LogCloseFold(3, "");
  if (!LOG_DIR.empty()) {
    ofstream outfile(fmt::format("{}/ref{}-acx.smt2", LOG_DIR,
                                 num_cx));
    fmt::print(outfile, "{}\n", reached);
  }
  
  if (!euforia_config.use_only_bmc_refinement) {
    bool refined;
    refined = RefineStates(reached);
    if (refined)
      goto refinement_done;

    refined = RefineSteps(reached);
    if (refined)
      goto refinement_done;
  }

  // solver_ = MakeSolver();
  // if (auto boolector = dynamic_pointer_cast<BoolectorSolver>(solver_)) {
  //   boolector->SetOption(BTOR_OPT_MODEL_GEN, 2);
  // }
  recent_lemmas_.clear();
  return RefineWithBmc(reached);

refinement_done:
  recent_lemmas_.clear();
  return unique_ptr<BoolectorCounterexample>(nullptr);
}

void AbstractChecker::Impl::collect_statistics(Statistics *st) const {
  solver_->collect_statistics(st);

  st->Update("refine_individual_time", stats_.refine_individual_time.count());
  st->Update("refine_step_time", stats_.refine_step_time.count());
  st->Update("refine_forward_time", stats_.refine_forward_time.count());
  st->Update("num_state_refinements", stats_.num_state_refinements);
  st->Update("num_step_refinements", stats_.num_step_refinements);
  st->Update("num_forward_refinements", stats_.num_forward_refinements);
  st->Update("num_interpolation_refinements", stats_.num_interpolation_refinements);
  st->Update("num_forward_lemmas", stats_.num_forward_lemmas);
  st->Update("num_onestep_lemmas", stats_.num_onestep_lemmas);
  st->Update("num_lemmas_with_select", stats_.num_lemmas_with_select);
  st->Update("num_lemmas_with_store", stats_.num_lemmas_with_store);
  st->Update("num_lemmas_with_bvnum", stats_.num_lemmas_with_bvnum);
  st->Update("num_lemmas_with_const_array", stats_.num_lemmas_with_const_array);
  st->Update("num_lemmas_with_array_ops", stats_.num_lemmas_with_array_ops);
  st->Update("num_layered_queries", stats_.num_layered_queries);
  st->Update("num_layered_spurious_queries", stats_.num_layered_spurious_queries);
  st->Update("num_concrete_array_queries", stats_.num_concrete_array_queries);
  
  st->Update("refinement_time", 
             stats_.refine_individual_time.count()+
             stats_.refine_step_time.count()+
             stats_.refine_forward_time.count());

  if (layered_abstractor_) {
    layered_abstractor_->collect_statistics(st);
  }

  if (symex_refine_) {
    symex_refine_->collect_statistics(st);
  }
}

const ExprSet
AbstractChecker::Impl::TSliceTransitionConstraints(const TSlice& tslice) {
  if (kUseTSlice) {
    return tslice.transition_constraints;
  }

  if (!trans_constraints_) {
    trans_constraints_ = ExprSet();
    copy(ExprConjunctIterator::begin(axsys_.trans()), ExprConjunctIterator::end(),
         std::inserter(*trans_constraints_, trans_constraints_->end()));
  }

  return *trans_constraints_;
}


//*-------------------------------------------------------------------------------*
//
  
bool AbstractChecker::Impl::LearnLemmaInSolver(
    const shared_ptr<AbstractLemmaClause>& lemma, const string&) {
  EDEBUG_CODE(
      // The lemma is the negation of an unsatisfiable formula, its concretized
      // negation should be unsatisfiable. That's what I'm testing here.
      logger.LogOpenFold(3, "ensuring that concretized lemma negation is unsat",
                         expr_not(lemma->as_expr()));
      shared_ptr<BtorWrapper> fresh_solver = make_shared<BtorWrapper>();
      auto lemma_negated = axsys_.Concretize(expr_not(lemma->as_expr()));
      Z3ToBtorRewriter z3_to_btor(fresh_solver);
      auto concrete_lemma = Z3BtorExprPair(lemma_negated,
                                           z3_to_btor.Rewrite(lemma_negated));
      fresh_solver->add(concrete_lemma.btor_node());
      auto result = fresh_solver->check();
      if (result == BtorWrapper::result::kSat) {
      cerr << *lemma << endl;
      EUFORIA_FATAL("!lemma is sat but should be unsat");
      }
      logger.LogCloseFold(3, "");
      );
  
  assert(axsys_.is_trans_formula(lemma->as_expr()));
  recent_lemmas_.push_back(lemma);

#if 0
  // it is possible to learn a lemma on X+ that implies the lemma holds on X because of the transition system somehow
  // but the lemmas should only be wrong if (1) the given lemmas and distinct-const-constraint and (2) the one-hot locations imply the lemma is redundante
  // check if lemma is implied by previous lemmas
  Z3Solver newsolver(axsys_.ctx());
  ExprSet assumps;
  for (auto& lemma : achk_->solver_->one_step_lemmas_) {
    assumps.insert(newsolver.trackAssertion(lemma->as_expr(), "one_step"));
  }
  for (auto& lemma : achk_->solver_->forward_lemmas_) {
    assumps.insert(newsolver.trackAssertion(lemma->as_expr(), "forward"));
  }
  // lemmas & !lemma is UNSAT
  newsolver.add(expr_not(lemma->as_expr()));
  if (newsolver.check() == z3::sat) {
    // lemma is irredundant
  } else {
    auto unsat_core = newsolver.unsat_core_reasons();
    fmt::print(std::cerr, "duplicate lemur:\n{}\n", *lemma);
    fmt::print(std::cerr, "reasons:\n{}\n", unsat_core);
    EUFORIA_FATAL("duplicate lemur");
  }
#endif

  // Sort the lemma and dump it to a unique file to make diffing work
  if (!LOG_DIR.empty()) {
    z3::expr_vector sorted_or(ctx());
    vector<z3::ExprWrapper> exprs(lemma->lits_begin(), lemma->lits_end());
    stable_sort(exprs.begin(), exprs.end());
    copy(exprs.begin(), exprs.end(), ExprVectorInserter(sorted_or));
    
    // Write to file
    string filename(fmt::format(
            "{}/ref{}-lemma{}.smt2",
            LOG_DIR, parent_.stats_.num_refinements+1, lemma->number));
    ofstream ofile;
    ofile.open(filename);
    fmt::print(ofile, "; lemma {}\n", lemma->number);
    z3::solver s(ctx());
    s.add(expr_mk_or(sorted_or));
    fmt::print(ofile, "{}\n", s.to_smt2());
    ofile.close();
  }

  achk_->AddLemma(lemma);
  return true;
}


shared_ptr<AbstractLemmaClause> AbstractChecker::Impl::MakeLemma(LemmaType ty) {
  switch (ty) {
    case LemmaType::kForward:
      stats_.num_forward_lemmas++; break;
    case LemmaType::kOneStep:
      stats_.num_onestep_lemmas++; break;
  }
  return make_shared<AbstractLemmaClause>(
      stats_.num_onestep_lemmas + stats_.num_forward_lemmas,
      ty, axsys_.ctx());
}


shared_ptr<AbstractLemmaClause>
AbstractChecker::Impl::LearnLemmas(const z3::expr& mus_abstract,
                                   const string& where) {
  // if it's a current state lemma, learn it on next, and vice versa
  VarInfoTraversal mus_info(axsys_);
  mus_info.Traverse(mus_abstract);
  bool has_current_vars = !mus_info.vars_used().empty(),
       has_next_vars    = !mus_info.vars_defd().empty(),
       has_inputs       = !mus_info.inputs_used().empty();
  
  // All lemmas set to forward because all are currently important to the
  // preimage computation
  const LemmaType ty = LemmaType::kForward;
  auto lemma = MakeLemma(ty);
  transform(ExprConjunctIterator::begin(mus_abstract), ExprConjunctIterator::end(),
            lemma->inserter(), distribute_expr_not);

  logger.Log(1, "learning lemma {} with {} literals", lemma->number,
             lemma->size());
  logger.Log(2, "[{}] {}", where, *lemma);
  if (has_inputs) { // transition lemma
    LearnLemmaInSolver(lemma, where);
  } else {
    LearnLemmaInSolver(lemma, where);
    if (has_current_vars && !has_next_vars) {
      auto next_lemma = MakeLemma(LemmaType::kForward); // forward b/c otherwise COI is excluded
      transform(lemma->lits_begin(), lemma->lits_end(),
                next_lemma->inserter(),
                [&](const z3::expr& e) { return axsys_.prime(e); });
      LearnLemmaInSolver(next_lemma, where);
      logger.Log(1, "(also learning lemma {} on next-state vars)",
                 next_lemma->number);
    } else if (!has_current_vars && has_next_vars) {
      auto curr_lemma = MakeLemma(LemmaType::kForward); // forward b/c otherwise COI is excluded
      transform(lemma->lits_begin(), lemma->lits_end(),
                curr_lemma->inserter(),
                [&](const z3::expr& e) { return axsys_.unprime(e); });
      LearnLemmaInSolver(curr_lemma, where);
      logger.Log(1, "(also learning lemma {} on current-state vars)",
                 curr_lemma->number);
    }
  }

  return lemma;
}



// Learn directly from an MUS. It must use only the correct variables. (X, Y, X')
// Returns a nullptr if no lemma was created because the MUS is vacuous.
shared_ptr<AbstractLemmaClause> AbstractChecker::Impl::RefineWithCore(
    const ExprSet& core, LemmaType /* XXX remove */, const string& where) {
  assert(!core.empty());
  auto abstract_expr = [&](const z3::expr& lit) {
    return axsys_.Abstract(lit).simplify(axsys_.simplify_params());
  };
  
  RMus rmus(*this, core);
  logger.Log(3, "concrete MUS {} has {} literals", addressof_void(rmus), rmus.size());
  logger.Log(4, "{{{{{{{}}}}}}}", rmus.as_expr());

  CharacterizeMus(rmus.as_expr());
  z3::expr_vector mus_abstract(ctx());
  boost::transform(rmus, ExprVectorInserter(mus_abstract), abstract_expr);
  return LearnLemmas(expr_mk_and(mus_abstract), where);
}


class IncrementStatOnceOnly {
 public:
  IncrementStatOnceOnly(int64_t *v) : v_(v), found_{} {}

  //! Increments the output stat the first time it is called; subsequent calls
  //! have no effect
  IncrementStatOnceOnly& operator++() {
    if (!found_) {
      (*v_)++;
      found_ = true;
    }
    return *this;
  }


  //! Returns whether increment has ever been called
  operator bool() const { return found_; }
  bool incremented() const { return found_; }

  IncrementStatOnceOnly operator&&(const IncrementStatOnceOnly& other) {
    IncrementStatOnceOnly ret(*this);
    ret.v_ = nullptr; // shouldn't be used
    ret.found_ = ret.found_ && other.found_;
    return ret;
  }

 private:
  int64_t *v_;
  bool found_;
};

inline void AbstractChecker::Impl::CharacterizeMus(const z3::expr& mus_expr) {
  IncrementStatOnceOnly select(&stats_.num_lemmas_with_select),
                        store(&stats_.num_lemmas_with_store),
                        const_num(&stats_.num_lemmas_with_bvnum),
                        const_array(&stats_.num_lemmas_with_const_array),
                        array_ops(&stats_.num_lemmas_with_array_ops);
  for (auto it = df_expr_iterator::begin(mus_expr),
       ie = df_expr_iterator::end(mus_expr); it != ie && 
       !(select.incremented() && store.incremented() &&
         const_num.incremented() && const_array.incremented() &&
         array_ops.incremented());
       ++it) {
    const auto& e = *it;
    if (!e.is_app()) { continue; }
    auto decl = e.decl();
    auto kind = decl.decl_kind();
    if (kind == Z3_OP_STORE) { ++store, ++array_ops; }
    if (kind == Z3_OP_SELECT) { ++select, ++array_ops; }
    if (kind == Z3_OP_CONST_ARRAY) { ++const_array, ++array_ops; }
    if (kind == Z3_OP_BNUM) { ++const_num; }
  }
}


// XXX check that the lemma is not valid in EUF
void AbstractChecker::Impl::CheckEufInvalidity(const AbstractLemmaClause& lemma) {
  Z3Solver solver(axsys_.ctx(), "QF_AUFBV");
  solver.Add(!lemma.as_expr());
  auto result = solver.Check();
  if (result == CheckResult::kUnsat) {
    // f is valid, this is an error
    fmt::print(cerr, "{}\n", lemma.as_expr());
    fmt::print(cerr, "lemma is valid in EUF -- this must not be\n");
    EUFORIA_FATAL("CheckEufInvalidity failed");
  }
}

/// check that the lemma abstractly refutes the formula (which was used concretely to derive the lemma)
void AbstractChecker::Impl::ValidateLemma(const AbstractLemmaClause& lemma,
                                          const z3::expr& acx_formula) {
  // check if lemma has any ites
  //class FindIte : public ExprVisitor<FindIte> {
  // public:
  //  void visitExpr(const z3::expr&) {}
  //  void visitITE(const z3::expr&) {
  //    assert(false && "ITE found in lemma");
  //  }
  //} ite_finder;
  //for (auto& lit : lemma.lits) {
  //  for_each(po_expr_iterator::begin(lit), po_expr_iterator::end(lit),
  //           ite_finder);
  //}
  Z3Solver solver(axsys_.ctx(), "QF_AUFBV");
  axsys_.AddTransitionsToChecker(solver);
  solver.Add(acx_formula);
  solver.Add(lemma.as_expr());

  auto result = solver.Check();
  if (result == CheckResult::kSat) {
    fmt::print(cerr, "ValidateLemma assertions:");
    for (auto assertion : solver.assertions()) {
      fmt::print(cerr, "{}\n", assertion);
    }
    auto model = solver.get_model();
      fmt::print(cerr, "lemma disjuncts under model\n");
    for (auto& lit : lemma.lits()) {
      fmt::print(cerr, "  {}: {}\n", lit,
                 model->Eval(lit));
    }
    fmt::print(cerr, "state vars under model\n");
    for (auto it = axsys_.vbegin(), ie = axsys_.vend(); it != ie; ++it) {
      const StateVar& v = *it;
      fmt::print(cerr, "  {}: {}, {}: {}\n", v.current(), model->Eval(v.current()),
                 v.next(), model->Eval(v.next()));
    }
    fmt::print(cerr, "constants under model\n");
    for (auto it = axsys_.constants_begin(), ie = axsys_.constants_end(); it != ie;
         ++it) {
      fmt::print(cerr, "  {}: {}\n", *it, model->Eval(*it));
    }
    fmt::print(cerr, "acx_formula under model\n");
    for (auto& elt : ExprConjuncts(acx_formula)) {
      fmt::print(cerr, "  {}: {}\n", elt, model->Eval(elt));
    }
    fmt::print(cerr, "Model: {}\n", *model);
    EUFORIA_FATAL("ValidateLemma failed");
  }
  assert(CheckResult::kUnsat == result);

  // CheckEufInvalidity(lemma);

  logger.Log(4, "ValidateLemma lemma validated");
}


bool AbstractChecker::Impl::RefineStates(
    const ReachabilityGraph& reached) {
  if (!refine_states_)
    return false;

  const auto& num_refinements = parent_.stats_.num_refinements;
  ++stats_.num_state_refinements;
  logger.Log(3, "refining states {} (RefineStates)",
             stats_.num_state_refinements);
  ScopedTimeKeeper t(&stats_.refine_individual_time);
  bool refined = false;
  size_t i = 0;
  
  if (euforia_config.use_layered_refinement_queries) {
    logger.Log(3, "performing layer-abstracted refinement checks");
    for (auto it = reached.cx_begin(), ie = reached.cx_end(); it != ie;
         ++it, i++) {
      shared_ptr<EufBvSolver> abs_solver =
          make_shared<EufBvSolver>(solver_, layered_abstractor_);
      StateRefiner abs_refine(*this, abs_solver, *it, num_refinements);
      auto core = abs_refine(i);
      if (core) {
        refined = true;
        stringstream ss;
        ss << "state_abstract:" << i;
        auto lemma = RefineWithCore(*core, LemmaType::kOneStep, ss.str());
        (void)lemma;
#ifdef EXPENSIVECHECKS
        abs_refine.ValidateLemma(*lemma);
#endif
      }
      ++stats_.num_layered_queries;
      if (abs_solver->is_concrete()) {
        stats_.num_layered_spurious_queries++;
      }
      if (!multiple_ && refined)
        break;
    }
  }

  if (!refined) {
    logger.Log(3, "performing concrete refinement checks");
    i = 0;
    for (auto it = reached.cx_begin(), ie = reached.cx_end(); it != ie;
         ++it, i++) {
      StateRefiner refine(*this, solver_, *it, num_refinements);
      auto core = refine(i);
      if (core) {
        refined = true;
        stringstream ss;
        ss << "state:" << i;
        auto lemma = RefineWithCore(*core, LemmaType::kOneStep, ss.str());
        (void)lemma;
#ifdef EXPENSIVECHECKS
        refine.ValidateLemma(*lemma);
#endif
      }
      if (refine.stats().num_arrays > 0) {
        stats_.num_concrete_array_queries++;
      }
      if (!multiple_ && refined)
        break;
    }
  }

  return refined;
}


bool AbstractChecker::Impl::RefineSteps(
    const ReachabilityGraph& reached) {
  const auto& num_refinements = parent_.stats_.num_refinements;
  ++stats_.num_step_refinements;
  logger.Log(3, "refining transitions {} (RefineSteps)",
             stats_.num_step_refinements);
  ScopedTimeKeeper t(&stats_.refine_step_time);
  bool refined = false;
  
  // check step z--i-->s in the Counterexample
  if (euforia_config.use_layered_refinement_queries) {
    logger.Log(3, "performing layer-abstracted refinement checks");
    for (auto it = reached.cx_begin(), ie = reached.cx_end();
         it != ie && it->has_transition(); ++it) {
      // XXX can be hoisted later
      shared_ptr<EufBvSolver> abs_solver =
          make_shared<EufBvSolver>(solver_, layered_abstractor_);
      StepRefiner abs_refine(*this, abs_solver, *it, num_refinements);
      abs_refine.set_uniq(".eufbv");
      auto core = abs_refine();
      if (core) {
        refined = true;
        stringstream ss;
        ss << "onestep_abstract*:A[" << it->state_index() <<
            "] & In[" << it->input_index() << 
            "] & T & A[" << it->next_state_index() << "]+";
        auto lemma = RefineWithCore(*core, LemmaType::kOneStep, ss.str());
        (void)lemma;
#ifdef EXPENSIVECHECKS
        abs_refine.ValidateLemma(*lemma);
#endif
      }
      ++stats_.num_layered_queries;
      if (abs_solver->is_concrete()) {
        stats_.num_layered_spurious_queries++;
      }
    }
  }

  if (!refined) {
    logger.Log(3, "performing concrete refinement checks");
    // check step z--i-->s in the Counterexample
    if (euforia_config.refinement_queries_without_t) {
      for (auto it = reached.cx_begin(), ie = reached.cx_end();
           it != ie && it->has_transition(); ++it) {
        StepRefinerWithoutT refine(*this, solver_, *it, num_refinements);
        auto core = refine();
        if (core) {
          refined = true;
          stringstream ss;
          ss << "onestep:A[" << it->state_index() << "] & In[" <<
              it->input_index() << "] & A[" << it->next_state_index() << "]+";
          auto lemma = RefineWithCore(*core, LemmaType::kOneStep, ss.str());
          (void)lemma;
#ifdef EXPENSIVECHECKS
          refine.ValidateLemma(*lemma);
#endif
        }
        if (refine.stats().num_arrays > 0) {
          stats_.num_concrete_array_queries++;
        }
      }
    }
    if (!refined) {
      for (auto it = reached.cx_begin(), ie = reached.cx_end();
           it != ie && it->has_transition(); ++it) {
        StepRefiner refine(*this, solver_, *it, num_refinements);
        auto core = refine();
        if (core) {
          refined = true;
          stringstream ss;
          ss << "onestep:A[" << it->state_index() << "] & In[" << 
              it->input_index() << "] & T & A[" << it->next_state_index() <<
              "]+";
          auto lemma = RefineWithCore(*core, LemmaType::kOneStep, ss.str());
          (void)lemma;
#ifdef EXPENSIVECHECKS
          refine.ValidateLemma(*lemma);
#endif
        }
        if (refine.stats().num_arrays > 0) {
          stats_.num_concrete_array_queries++;
        }
      }
    }
  }
  
  logger.Log(3, "RefineSteps took {} ms [onestep eavg: {:.3f} s]",
             t.Get().count(), -0.001 /*T.avg*/);
  return refined;
}


shared_ptr<symex::State> AbstractChecker::Impl::CheckInitialState(
    symex::Executor& symex, const ReachabilityGraph& reached) {
  auto concretize = [&](auto&& e) { return axsys_.Concretize(e); };
  TimerDuration d(0);
  ScopedTimeKeeper t(&d);
  ExprSet init_concrete;
  boost::transform(reached.init(),
                   inserter(init_concrete, init_concrete.begin()), concretize);
  boost::transform(ExprConjuncts(axsys_.init_state()),
                   inserter(init_concrete, init_concrete.begin()), concretize);
  auto sym = symex.InitState(init_concrete);
  logger.Log(5, "initial concrete (symbolic) state: {}", *sym);
  if (!symex.CheckState(sym)) {
    logger.Log(3, "I & A[0] is CUNSAT [{} s]", t.get().count());
    auto core = solver_->unsat_core();
    auto core_set = ExprSet(core.begin(), core.end());
    stringstream ss;
    ss << "forward:" << "I & A[0]";
    auto lemma = RefineWithCore(core_set, LemmaType::kForward, ss.str());
#ifdef EXPENSIVECHECKS
    z3::expr init_formula(ctx());
    boost::copy(init_concrete, ExprAndInserter(init_formula));
    ValidateLemma(*lemma, init_formula);
#endif
    return shared_ptr<symex::State>(nullptr);
  } else {
    auto model = symex.get_model();
    sym->set_pre_step_model(model); // XXX doesn't need to be done in initial state
  }
  logger.Log(3, "I & A[0] is CSAT [{} s]", t.get().count());
  return sym;
}


#if 0
unique_ptr<BoolectorCounterexample>
AbstractChecker::Impl::RefineWithBmcSpacer(const ReachabilityGraph& reached) {
  ++stats_.num_forward_refinements;
  logger.Log(3, "refining forward from initial state (RefineWithBmc)");
  ScopedTimeKeeper t(&stats_.refine_forward_time);
  bool refined = false;
  auto cx = std::make_unique<BoolectorCounterexample>(solver().btor_solver());

  z3::fixedpoint fp(ctx());
  z3::params fp_params(ctx());
  fp_params.set("engine", "spacer");
  // fp_params.set("validate", true);
  // disable inlining per Nikolaj: https://github.com/Z3Prover/z3/pull/1646
  fp_params.set("xform.inline_eager", false);
  fp_params.set("xform.inline_linear", false);
  fp.set(fp_params);
  // fmt::print(std::cerr, "{}\n", fp.help());
  // abort();
  OrderedExprSet state_vars;
  z3::expr_vector input_vars(ctx());
  transform(cxsys_.vbegin(), cxsys_.vend(),
            std::inserter(state_vars, state_vars.end()),
            [&](auto&& v) { return v.current(); });
  transform(cxsys_.ibegin(), cxsys_.iend(),
            ExprVectorInserter(input_vars),
            [&](auto&& i) { return static_cast<z3::expr>(i); });
  auto ToSortVector = [&](const OrderedExprSet& s) {
    z3::sort_vector sorts(ctx());
    for (const z3::expr& e : s) {
      sorts.push_back(e.get_sort());
    }
    return sorts;
  };
  auto ToExprVector = [&](const OrderedExprSet& s, bool next = false) {
    z3::expr_vector exprs(ctx());
    for (const z3::expr& e : s) {
      exprs.push_back(next ? cxsys_.prime(e) : e);
    }
    return exprs;
  };

  // t_0, t_1, ..., t_n should be unsat. what if it isn't? have to deal with
  // that case
  // x_i is fv(t1 ... t_i) intersect fv(t_i+1 ... t_n)
  int i = 0;
  z3::func_decl p_i(ctx()), p_i_next(ctx());
  z3::expr_vector x_i(ctx()), x_i_next(ctx());
  z3::sort_vector s_i(ctx()), s_i_next(ctx()); // sorts of corresponding x_i
  std::string name_p_i, name_p_i_next;
  for (auto it = reached.cx_begin(), ie = reached.cx_end(); it != ie;
       ++it, ++i) {
    x_i = ToExprVector(state_vars);
    s_i = ToSortVector(state_vars);
    if (i == 0) { //&it->state() == &reached.init()) {
      name_p_i = "p_" + to_string(i);
      p_i      = ctx().function(name_p_i.c_str(), s_i, ctx().bool_sort());
      fp.register_relation(p_i);
      auto rule = z3::forall(x_i, p_i(x_i));
      fp.add_rule(rule, ctx().str_symbol("init"));
    }
    if (it->HasTransition()) {
      name_p_i_next = "p_" + to_string(i+1);
      x_i_next      = ToExprVector(state_vars, true);
      s_i_next      = ToSortVector(state_vars);
      p_i_next      = ctx().function(name_p_i_next.c_str(), s_i_next,
                                     ctx().bool_sort());
      fp.register_relation(p_i_next);
      const auto& slice_i = it->state_transition();
      z3::expr t_i = axsys_.Concretize(
          expr_and(axsys_.prime(AndExprSet(ctx(), slice_i.target_constraints)),
                   AndExprSet(ctx(), TSliceTransitionConstraints(slice_i))));
      z3::expr_vector x_all(ctx());
      for (unsigned j = 0; j < x_i.size(); j++) {
        x_all.push_back(x_i[j]);
      }
      for (unsigned j = 0; j < input_vars.size(); j++) {
        x_all.push_back(input_vars[j]);
      }
      for (unsigned j = 0; j < x_i_next.size(); j++) {
        x_all.push_back(x_i_next[j]);
      }
      auto rule = z3::forall(x_all,
                             z3::implies(p_i(x_i) && t_i, p_i_next(x_i_next)));
      fp.add_rule(
          rule, ctx().str_symbol((name_p_i + " -> " + name_p_i_next).c_str()));

      p_i      = p_i_next;
      name_p_i = name_p_i_next;
    } else {
      // last state implies false
      fmt::print(std::cerr, "{}", fp);
      auto query = z3::exists(x_i, p_i(x_i));
      auto result = fp.query(query);
      fmt::print(stderr, "query result: {}\n", result);
      if (result == z3::check_result::sat ||
          result == z3::check_result::unsat) {
      // sat = counterexample
      // unsat = interpolants
        fmt::print(stderr, "answer:\n{}\n", fp.get_answer());
      }
        abort();
    }
  }


  if (refined)
    return unique_ptr<BoolectorCounterexample>(nullptr);

  logger.Log(1, "refinement found Counterexample");
  // true positive!
  return cx;
}
#endif


unique_ptr<Counterexample>
AbstractChecker::Impl::RefineWithBmcOneShot(const ReachabilityGraph& reached) {
  shared_ptr<Solver> solver = solver_;
  if (euforia_config.use_layered_refinement_queries) {
    logger.Log(3, "performing layer-abstracted check");
    solver = std::make_unique<EufBvSolver>(solver, layered_abstractor_);
  }
  BmcOneShotRefiner refine(*this, solver, reached,
                           parent_.stats_.num_refinements);
  bool refined = false;
  auto learn_from_cores = [&](auto&& cores) -> unique_ptr<Counterexample> {
    if (cores) {
      ++stats_.num_interpolation_refinements;
      for (const auto& core_expr : *cores) {
        stringstream ss;
        ss << "bmc:";
        auto where = ss.str();
        ExprSet core(ExprConjunctIterator::begin(core_expr),
                     ExprConjunctIterator::end());
        refined |= bool(RefineWithCore(core, LemmaType::kForward, where));
      }
      assert(refined);
      return unique_ptr<BoolectorCounterexample>(nullptr);
    } else {
      return refine.make_counterexample();
    }
  };

  // Refine first, possible a second time if use_layered_refinement_queries is
  // true.
  auto cores = refine();
  if (cores) {
    return learn_from_cores(cores);
  } else {
    if (euforia_config.use_layered_refinement_queries) {
      refine.set_solver(solver_);
      cores = refine();
    }
    return learn_from_cores(cores);
  }
  EUFORIA_FATAL("impossible");
}


unique_ptr<Counterexample>
AbstractChecker::Impl::RefineWithBmc(const ReachabilityGraph& reached) {
  const auto& num_refinements = parent_.stats_.num_refinements;
  ++stats_.num_forward_refinements;
  logger.Log(3, "refining forward from initial state (RefineWithBmc)");

  if (euforia_config.use_one_shot_bmc_refinement) {
    ScopedTimeKeeper t(&stats_.refine_forward_time);
    return RefineWithBmcOneShot(reached);
  }

  ScopedTimeKeeper t(&stats_.refine_forward_time);
  // auto cx = std::make_unique<BoolectorCounterexample>(solver_.btor_solver());
  auto cx = std::make_unique<SCounterexample>();
  auto& cx_states = cx->states_;
  // auto& cx_inputs = cx->cinputs;
  symex::Executor symex(axsys_, *solver_);

  auto symbolic_curr = CheckInitialState(symex, reached);
  if (!bool(symbolic_curr)) {
    // found refinement
    return unique_ptr<BoolectorCounterexample>(nullptr);
  }
  cx_states.push_back(symbolic_curr);

  symex_refine_ = make_unique<BmcSymexRefiner>(*this, solver_, num_refinements);
  // step concrete cx, constructed incrementally, along acx as a guide
  // i - index into cx
  bool refined = false;
  size_t i = 0;
  for (auto it = reached.cx_begin(), ie = reached.cx_end();
       it != ie && it->HasTransition(); ++it) {
    assert(cx_states.size() == i+1);
    logger.Log(3, "query cx[{}] & In[{}] & T & A[{}]+ (acx length {})",
               i, it->input_index(), it->next_state_index(),
               reached.cx_length());
    
    BmcSymexRefiner::CoreOrNewState result =
        (*symex_refine_)(*it, symbolic_curr);
    if (auto *core = boost::get<ExprSet>(&result)) {
      stringstream label;
      label << "forward:" << "curr & In[" << it->input_index() << "] & T";
      auto lemma = RefineWithCore(*core, LemmaType::kForward, label.str());
      (void)lemma;
#ifdef EXPENSIVECHECKS
      refine.ValidateLemma(*lemma);
#endif
      refined = true;
      break;
    } else if (auto *new_state =
               boost::get<shared_ptr<symex::State>>(&result)) {
      // query was SAT
      symbolic_curr = *new_state;
      cx_states.push_back(symbolic_curr);
      i++;
    } else {
      EUFORIA_FATAL("baaaaad variant");
    }
  }
  
  logger.Log(3, "RefineWithBmc took {} ms [fwd eavg: {:.3f} s]",
             t.Get().count(), -0.001/*timer.avg*/);

  if (refined)
    return unique_ptr<BoolectorCounterexample>(nullptr);

  logger.Log(1, "refinement found counterexample");
  // true positive!
  return cx;
} 

} // end namespace euforia
