// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "xsys/abstract_vmt_transition_system.h"

#include "checker.h"
#include "cube.h"
#include "existential_elimination.h"
#include "normalize_abstract_expr.h"
#include "supp/equality_literal.h"
#include "supp/euforia_config.h"
#include "supp/expr_iterators.h" // df/po iterators
#include "supp/statistics.h"
#include "tslice.h"
#include "xsys/influence_traversal.h"
#include "xsys/var_info_traversal.h"
#include "supp/expr_flattener.h"
#include "supp/fmt_supp.h"


using namespace std;
using namespace llvm;


namespace euforia {
namespace vmt {

// The transition system should support two kinds of representations. One is a
// cone-based representation where each variable has a single expr that defines
// its next-state. In this representation, preimages will be computed by
// iterating over the next-state variables (starting with the variables in the
// target cube) and traversing the equations for each variable encountered. 
//
// In the second representation, there is no structure -- there's just a
// transition relation. Preimage is computed by pruning the model and
// collecting all the terms found. This is what's happening now.


/*----------------------------------------------------------------------------*/

struct EufStats : public ExprVisitor<EufStats> {
  ExprMap<unsigned int> eocc; // occurrences of given expression
  AstMap<unsigned int> docc; // occurrences of given declaration
  z3::context& ctx;

  EufStats(z3::context& c) : ctx(c) {}

  void traverse(const z3::expr& e) {
    for (auto I = df_expr_iterator::begin(e), E = df_expr_iterator::end(e); I != E; ++I) {
      visit(*I);
    }
  }

  void visitExpr(const z3::expr& e) {
    eocc[e]++;
    docc[e.decl()]++;
  }

  void collect_statistics(Statistics *st) const;
};

void EufStats::collect_statistics(Statistics *st) const {
  int64_t num_uf_decls = 0, num_uf_occurrences = 0, num_up_decls = 0, 
          num_up_occurrences = 0, num_uconst_decls = 0,
          num_uconst_occurrences = 0;
  for (auto& [d, cnt] : docc) {
    if (IsUFunction(static_cast<const z3::func_decl&>(d))) {
      num_uf_decls++;
      num_uf_occurrences += cnt;
    } else if (IsUPredicate(static_cast<const z3::func_decl&>(d))) {
      num_up_decls++;
      num_up_occurrences += cnt;
    } else if (IsUConstant(static_cast<const z3::func_decl&>(d))) {
      num_uconst_decls++;
      num_uconst_occurrences += cnt;
    }
  }

  int64_t num_exprs = 0;
  for (const auto& [expr, cnt] : eocc) {
    (void)expr;
    num_exprs += cnt;
  }

#define output_stat(stat) st->Update(#stat, static_cast<int64_t>(stat))

  int64_t num_decls = docc.size();
  output_stat(num_decls);
  output_stat(num_uf_decls);
  output_stat(num_uf_occurrences);
  output_stat(num_up_decls);
  output_stat(num_up_occurrences);
  output_stat(num_uconst_decls);
  output_stat(num_uconst_occurrences);
  int64_t num_distinct_exprs = eocc.size();
  output_stat(num_distinct_exprs);
  output_stat(num_exprs);

#undef output_stat
}

std::ostream& operator<<(std::ostream& os, const EufStats& stats) {
#if YOU_WANT_TOO_MUCH_INFO
  for (auto& [d, cnt] : stats.docc) {
    auto s = Z3_func_decl_to_string(stats.ctx, (z3::func_decl&)d);
    os << s << ": " << cnt << endl;
  }
#endif

  int64_t num_uf_decls = 0, num_uf_occurrences = 0, num_up_decls = 0, 
          num_up_occurrences = 0, num_uconst_decls = 0,
          num_uconst_occurrences = 0;
  for (auto& [d, cnt] : stats.docc) {
    if (IsUFunction(static_cast<const z3::func_decl&>(d))) {
      num_uf_decls++;
      num_uf_occurrences += cnt;
    } else if (IsUPredicate(static_cast<const z3::func_decl&>(d))) {
      num_up_decls++;
      num_up_occurrences += cnt;
    } else if (IsUConstant(static_cast<const z3::func_decl&>(d))) {
      num_uconst_decls++;
      num_uconst_occurrences += cnt;
    }
  }

  int64_t num_exprs = 0;
  for (const auto& [expr, cnt] : stats.eocc) {
    (void)expr;
    num_exprs += cnt;
  }

#define output_stat(stat) os << #stat << ": " << stat << endl

  int64_t num_decls = stats.docc.size();
  output_stat(num_decls);
  output_stat(num_uf_decls);
  output_stat(num_uf_occurrences);
  output_stat(num_up_decls);
  output_stat(num_up_occurrences);
  output_stat(num_uconst_decls);
  output_stat(num_uconst_occurrences);
  int64_t num_distinct_exprs = stats.eocc.size();
  output_stat(num_distinct_exprs);
  output_stat(num_exprs);

#undef output_stat

  return os;
}

/*----------------------------------------------------------------------------*/
struct AbstractVmtTransitionSystem::Stats {
  const AbstractVmtTransitionSystem& xsys;

  int64_t preimage_num_expansions;
  int64_t exp_avg_horizon;
  ExpAvg avg_preimage_size;
  ExpAvg avg_preimage_num_constants;
  ExpAvg avg_preimage_num_state_vars;
  ExpAvg avg_preimage_num_equalities;
  ExpAvg avg_preimage_num_disequalities;
  ExpAvg avg_preimage_num_distincts;
  ExpAvg avg_preimage_distinct_size;
  ExpAvg avg_preimage_num_boolean_vars;
  ExpAvg avg_preimage_num_ufs;
  ExpAvg avg_preimage_num_ups;
  TimerDuration expand_preimage_time;
  int64_t eager_constant_num_constraints;
  
  Stats(const AbstractVmtTransitionSystem& xsys, int exp_avg_horizon = 50)
      : xsys(xsys), preimage_num_expansions(0), exp_avg_horizon(exp_avg_horizon),
      avg_preimage_size(exp_avg_horizon), avg_preimage_num_constants(exp_avg_horizon),
      avg_preimage_num_state_vars(exp_avg_horizon),
      avg_preimage_num_equalities(exp_avg_horizon),
      avg_preimage_num_disequalities(exp_avg_horizon),
      avg_preimage_num_distincts(exp_avg_horizon),
      avg_preimage_distinct_size(exp_avg_horizon),
      avg_preimage_num_boolean_vars(exp_avg_horizon),
      avg_preimage_num_ufs(exp_avg_horizon), avg_preimage_num_ups(exp_avg_horizon),
      expand_preimage_time(0), eager_constant_num_constraints(0)  {}
};

//^----------------------------------------------------------------------------^
// Impl
class AbstractVmtTransitionSystem::Impl {
 public:
  unique_ptr<NormalizeAbstractExpr> normalize_;
  unique_ptr<ExprSet> predicates_;

  Impl(AbstractVmtTransitionSystem& axsys) 
      : normalize_(std::make_unique<NormalizeAbstractExpr>()),
        predicates_(std::make_unique<ExprSet>()),
        axsys_(axsys), trans_rest_(axsys.ctx()) {}
  Impl(Impl&) = delete;
  Impl& operator=(Impl&) = delete;

  inline void LemmaInfluence(CheckerSat& cs, InfluenceTraversal& influence,
                        const shared_ptr<AbstractModel>& this_model) const {
    logger.LogOpenFold(5, "collecting terms from lemmas");
    for (const auto& lemma : cs.forward_lemmas()) {
      bool found_sat_lit = false;
      for (auto& lit : lemma->lits()) {
        if (this_model->Satisfies(lit)) {
          // XXX try moving this lit to front to see if that helps
          logger.Log(5, "lemma {} has satisfied literal: {}", lemma->number, lit);
          //this_model->Add(lit);
          influence(ExprSet({lit}));
          found_sat_lit = true;
          break;
        }
      }
      _unused(found_sat_lit); // for when asserts disabled
      assert(found_sat_lit);
    }
    logger.LogCloseFold(5, "");
  }

  
  inline void CalculateStats(const Cube& preimage, Stats *stats) const {
    for (auto& lit : preimage) {
      if (is_eq(lit)) {
        stats->avg_preimage_num_equalities += 1;
      }
      if (is_not(lit) && is_eq(lit.arg(0))) {
        stats->avg_preimage_num_disequalities += 1;
      }
      if (is_distinct(lit)) {
        stats->avg_preimage_num_distincts += 1;
        stats->avg_preimage_distinct_size += lit.num_args();
      }
      if (IsUFunction(lit)) {
        stats->avg_preimage_num_ufs += 1;
      }
      if (IsUPredicate(lit) || (is_not(lit) && IsUPredicate(lit.arg(0)))) {
        stats->avg_preimage_num_ups += 1;
      }
    }
    stats->avg_preimage_size += preimage.size();
    if (stats->preimage_num_expansions % stats->exp_avg_horizon == 0) {
      Statistics st;
      axsys_.collect_statistics(&st);
      logger.Log(StatLog(3), "preimage stats [over last {} expansions]:\n",
                 stats->exp_avg_horizon);
      logger.Log(StatLog(3), "{}", st);
    }
  }

  // Finds all the toplevel equations and stashes them in trans_equations_. An
  // equation is either (<input> = <thing>) or (<next-state-var> = <thing>).
  // Any top-level conjunct that isn't an equation is put into trans_rest.
  // After this function, trans() is equivalent to trans_rest() && (conjunction
  // of equations from trans_equations()).
  template <typename It>
  void PartitionTransEquations(It it, It ie) {
    logger.Log(3, "partitioning trans equations");
    z3::expr_vector rest(trans_rest_.ctx());
    ExprVectorInserter trans_rest_out(rest);
    for (; it != ie; ++it) {
      // Z3 likes ANDs and ORs to be flattened; ANDs especially. But its
      // rewriting algorithm sucks when there are huge nested ANDs. This
      // flattens them them using an algorithm that doesn't suck.
      ExprFlattener flatten;
      auto e = flatten(*it);
      if (detect_equalities_ && EqualityLiteral::is_equality(e)) {
        EqualityLiteral eq_lit(e);
        // We *might* want to add an equality lit to trans_rest: if it can't be
        // rewritten as (<next-state> = <something>) or (<input> = <something>).
        bool added = false;
        if (axsys_.HasNextStateVar(eq_lit.lhs()) ||
            axsys_.FindInput(eq_lit.lhs())) {
          // There is a rare case where having equations (x=y) where x is never
          // referred to (1) on the rhs of any other equation and (2) in
          // trans_rest; this means it will never be looked up during preimage
          // expansion. In order for this to be a problem, there must be a
          // second equation (x=z), because otherwise (x=y) is only
          // constraining x, not y.
          if (trans_equations_.find(eq_lit.lhs()) == trans_equations_.end()) {
            trans_equations_.insert({eq_lit.lhs(), eq_lit.rhs()});
            added = true;
          }
        }
        if (axsys_.HasNextStateVar(eq_lit.rhs()) ||
            axsys_.FindInput(eq_lit.rhs())) {
          eq_lit.swap();
          if (trans_equations_.find(eq_lit.lhs()) == trans_equations_.end()) {
            trans_equations_.insert({eq_lit.lhs(), eq_lit.rhs()});
            added = true;
          }
        }
        if (added)
          continue;
      }
      logger.Log(5, "couldn't find equality in clause {}", e);
      *trans_rest_out++ = e;
    }

    logger.Log(3, "found {} toplevel equations", trans_equations_.size());
    for (auto& [var, rhs] : trans_equations_) {
      logger.Log(5, "    {} = {}", var, rhs);
    }
    trans_rest_ = expr_mk_and(rest);
    logger.Log(5, "rest of transition relation:\n    {}", trans_rest_);
  }


  inline const ExprMultiMap<z3::expr>& trans_equations() const {
    return trans_equations_;
  }

  inline z3::expr trans_rest() const {
    return trans_rest_;
  }

 private:
  AbstractVmtTransitionSystem& axsys_;
  ExprMultiMap<z3::expr> trans_equations_;
  z3::expr trans_rest_;
  const bool detect_equalities_ = true;
};

/*----------------------------------------------------------------------------*/
  
AbstractVmtTransitionSystem::~AbstractVmtTransitionSystem() = default;

AbstractVmtTransitionSystem::AbstractVmtTransitionSystem(
    ConcreteVmtTransitionSystem& sts, const config::Config& c)
  : VmtTransitionSystem(sts), cts_(sts), stats_(std::make_unique<Stats>(*this)),
    pimpl_(std::make_unique<Impl>(*this)) {


  // Add all state variables (except bool) with new ones of type term
  ExprMap<z3::expr> var_subst; // XXX delete and delete from constructor below
  absman_ = std::make_unique<AbstractionManager>(ctx(), var_subst);
  absman_->set_abstract_arrays(!c.no_abstract_arrays);
  absman_->set_abstract_array_select_fresh(c.abstract_array_select_fresh);

  auto vmcopy(vars_); // copy because we're going to delete
  for (const auto& old_name_and_var : vmcopy) {
    const StateVar& oldVar = *old_name_and_var.second;
    if (oldVar.is_location()) continue; // skip locations
    if (oldVar.current().is_bool()) continue;
    auto current = Abstract(oldVar.current());
    auto next = Abstract(oldVar.next());
    auto name = current.decl().name().str();
    auto sort = current.get_sort();
    assert(z3::eq(current.get_sort(), next.get_sort()));
    unique_ptr<StateVar> var;
    if (sort.is_array())
      var = std::make_unique<TermArrayStateVar>(name, current, next);
    else if (!sort.is_bool())
      var = std::make_unique<TermStateVar>(name, current, next);
    else
      var = std::make_unique<PlainStateVar>(name, current, next);
    AddVar(move(var));
    DeleteVar(oldVar.name());
  }


  auto imcopy(inputs_);
  for (auto& p : imcopy) {
    const PrimaryInput& oldInput = *p.second;
    if (oldInput.z.is_bool()) continue;
    auto z = Abstract(oldInput.z);
    auto name = z.decl().name().str();
    unique_ptr<PrimaryInput> inp;
    if (!z.get_sort().is_bool()) {
      inp = std::make_unique<TermPrimaryInput>(name, z);
    } else {
      assert(z.get_sort().is_bool());
      inp = std::make_unique<PlainPrimaryInput>(name, z);
    }
    AddInput(move(inp));
    DeleteInput(oldInput.name);
  }

  // rewrite as abstract system
  //getT().rewriteConstraints(*absman, var_subst);
  logger.Log(5, "abstracting concrete transition system");
  auto abstract_system = [&](const z3::expr& e) { 
    return Abstract(e);
  };
  RewriteSystem(abstract_system);

  pimpl_->PartitionTransEquations(ExprConjunctIterator::begin(trans()),
                                  ExprConjunctIterator::end());
}

z3::expr AbstractVmtTransitionSystem::trans_rest() const {
  return pimpl_->trans_rest();
}

boost::optional<AbstractVmtTransitionSystem::EquationMapRef>
AbstractVmtTransitionSystem::trans_equations() const {
  return boost::optional<EquationMapRef>(pimpl_->trans_equations());
}

std::ostream& AbstractVmtTransitionSystem::Print(std::ostream& os) const {
  os << "AbstractVmtTransitionSystem:" << endl;

  os << "eager_constant_ordering: " << eager_constant_ordering_ << endl;

  VmtTransitionSystem::Print(os);
  fmt::print(os, "T equations:\n");
  if (auto eq_map = trans_equations()) {
    for (const auto& [lhs, rhs] : eq_map->get()) {
      fmt::print(os, "  {} = {}\n", lhs, rhs);
    }
  }
  fmt::print(os, "T rest:\n");
  fmt::print(os, "{}\n", trans_rest());
  //if (!LOG_DIR.empty()) {
  //  ofstream f(LOG_DIR + "/abs_trans.dot");
  //  ExprDotFormatter format(f);
  //  format.Print({trans()});
  //}
  // VmtTransitionSystem::Print(os);
  fmt::print(os, "legends for equations\n");
  ExprLegend legend;
  if (auto eq_map = trans_equations()) {
    for (const auto& [lhs, rhs] : eq_map->get()) {
      auto eq = static_cast<z3::expr>(lhs) == rhs;
      legend.Print(os, eq);
    }
  }
  fmt::print(os, "legend for trans_rest()\n");
  legend.Print(os, trans_rest());
  fmt::print(os, "legend for init_state()\n");
  legend.Print(os, init_state());
  fmt::print(os, "legend for property()\n");
  legend.Print(os, property());
  return os;
}

void AbstractVmtTransitionSystem::PrintStats(std::ostream& out) const {
  EufStats stats(ctx());
  stats.traverse(init_state());
  stats.traverse(property());
  stats.traverse(trans());
  stringstream os;
  os << stats;
  os << "num_state_vars: " << num_vars() << endl;
  os << "num_inputs: " << num_inputs() << endl;
  os << "num_locations: " << ip_repr().current().getBools().size() << endl;
  fmt::print(os, "num_trans_equations: {}\n", trans_equations()->get().size());
  out << os.str();
}

void
AbstractVmtTransitionSystem::collect_static_statistics(Statistics *st) const {
  EufStats stats(ctx());
  stats.traverse(init_state());
  stats.traverse(property());
  stats.traverse(trans());
  stringstream os;
  stats.collect_statistics(st);
  st->Update("num_locations",
             static_cast<int64_t>(ip_repr().current().getBools().size()));
  st->Update("num_trans_equations",
             static_cast<int64_t>(trans_equations()->get().size()));
}

void AbstractVmtTransitionSystem::collect_statistics(Statistics *st) const {
#define upd(stat) st->Update(#stat, stats_->stat)
#define upd_time(stat) st->Update(#stat, stats_->stat.count())
#define upd_running(stat) st->Update(#stat, stats_->stat.get())
  upd(preimage_num_expansions);
  upd(eager_constant_num_constraints);
  upd_time(expand_preimage_time);
  upd(exp_avg_horizon);
  upd_running(avg_preimage_size);
  upd_running(avg_preimage_num_constants);
  st->Update("avg_preimage_num_constants_pct_of_total",
             stats_->avg_preimage_num_constants.percent(constants().size()));
  upd_running(avg_preimage_num_state_vars);
  st->Update("avg_preimage_num_state_vars_pct_of_total",
             stats_->avg_preimage_num_state_vars.percent(num_vars()));
  upd_running(avg_preimage_num_boolean_vars);
  upd_running(avg_preimage_num_equalities);
  upd_running(avg_preimage_num_disequalities);
  upd_running(avg_preimage_num_distincts);
  upd_running(avg_preimage_distinct_size);
  upd_running(avg_preimage_num_ufs);
  upd_running(avg_preimage_num_ups);
#undef upd
#undef upd_time
#undef upd_running
}

void AbstractVmtTransitionSystem::AddDistinctConstConstraint(Solver& LC) const {
  LC.Add(get_abstract_background());
}

z3::expr AbstractVmtTransitionSystem::get_abstract_background() const {
  z3::expr_vector v(ctx());
  auto constsBySort = absman_->GetConstsBySort();
  for (auto& consts : constsBySort) {
    v.push_back(expr_distinct(consts.second));
  }
  return expr_mk_and(v);
}


shared_ptr<AbstractModel> AbstractVmtTransitionSystem::GetModel(const shared_ptr<Model>&) const {
  abort();
#if 0
  auto ret = make_shared<AbstractModel>(m, *this, &absman->decls());
  ExprSet assumps;
  fast_simplify_transitions_with_model simplifier(*this, *ret, assumps, true);
  for (auto it = vbegin(), ie = vend(); it != ie; ++it) {
    ret->add(it->current());
    //Cube tmp;
    auto nxt = simplifier.RewriteNextState(it->next());
    ret->add(it->next() == nxt);
    //      fullAM->add(findNextState(model, *it, getT().getNextState(*it), tmp, modelSimplifyCache));
    //      fullAM->add(tmp.begin(), tmp.end());
  }
  //for (auto& [_, eq] : str.auxEquations) {
  //  ret->add(eq);
  //}
  return ret;
#endif
}

const char *AbstractVmtTransitionSystem::solver_logic() const {
  // XXX ideally, detect that if there are no arrays we can use QF_UF instead
  if (euforia_config.no_abstract_arrays) {
    return "QF_AUFBV";
  } else {
    return "QF_UF";
  }
}


/*-----------------------------------------------------------------------------------*/
// preimage helpers


shared_ptr<AbstractModel>
AbstractVmtTransitionSystem::ExpandedPreimage(
    CheckerSat& CS, const std::shared_ptr<Model>& model, const Cube& s, // target
    Cube& z/*out*/, shared_ptr<TSlice> *this_tslice/*out*/) const {
  ScopedTimeKeeper t(&stats_->expand_preimage_time);
  ++stats_->preimage_num_expansions;
  auto s_next = s.asExprNext();

  LOG(5, "begin computing abstract preimage for s+ (Cube {}): {}", s.ID, s_next);

  *this_tslice = make_shared<TSlice>();
  (*this_tslice)->target_constraints.insert(s.nbegin(), s.nend());

  logger.LogOpenFold(5, "full z3 model:");
  logger.LogCloseFold(5, "{}", *model);
  auto this_model = make_shared<AbstractModel>(model, *this, &absman_->decls());

  // rewrite constraints, collect assumptions
  auto& predicates = *pimpl_->predicates_;
  predicates.clear();
  auto eval = [&](const z3::expr& e, bool c) {
    return this_model->Eval(e, c);
  };
  InfluenceTraversal influence(*this, eval, &predicates);

  logger.LogOpenFold(5, "collecting terms from s_next");
  ExprSet s_next_terms(s.nbegin(), s.nend());
  //for (const auto& term : s_next_terms) {
  //  this_model->Add(term);
  //}
  influence(s_next_terms);
  logger.LogCloseFold(5, "");

  // auto new_num_assumps = predicates.size();
  //const auto s_next_num_assumps = new_num_assumps;
  //const auto before_lemma_visits = influence.GetAndResetNumVisits();

  if (!CS.forward_lemmas().empty()) {
    pimpl_->LemmaInfluence(CS, influence, this_model);
  }

  //auto lemma_num_assumps = predicates.size() - new_num_assumps;
  // new_num_assumps = predicates.size();
  //const auto after_lemma_visits = influence.GetAndResetNumVisits();
  auto vars_defd = influence.vars_defd;
  //auto tslice_num_assumps = predicates.size() - new_num_assumps;
  // new_num_assumps = predicates.size();
  // (void)new_num_assumps;

  logger.LogOpenFold(6, "adding predicates to model");
  for (auto& c : influence.constants_used) {
    this_model->Add(c);
  }
  stats_->avg_preimage_num_constants += influence.constants_used.size();
  for (const z3::expr& v : influence.vars_used) {
    this_model->Add(v);
    if (v.is_bool()) {
      stats_->avg_preimage_num_boolean_vars += 1;
    }
  }
  stats_->avg_preimage_num_state_vars += influence.vars_used.size();
  LOG(5, "defd state vars: {}", vars_defd);
  LOG(5, "used state vars: {}", influence.vars_used);

  //ExistentialElimination ee(ctx(), ExistentialElimination::Config::kBestEffort);
  //ExprSet vars_elim;
  //for (auto& l : predicates) {
  //  VarInfoTraversal info(*this);
  //  info.Traverse(l);
  //  for (auto& i : info.inputs_used()) {
  //    vars_elim.insert(i);
  //  }
  //}
  //predicates = ee.ElimCube(vars_elim, predicates);

  VarInfoTraversal info_traversal(*this);
  // Any preds found, add them to this_model
  int num_assumps = 0;
  while (!predicates.empty()) {
    info_traversal.Reset();
    ++num_assumps;
    z3::expr predicate = *predicates.begin();
    predicates.erase(predicate);
    info_traversal.Traverse(predicate);
    LOG(6, "predicate found (used: {} defd: {} inputs: {}): {}",
        info_traversal.vars_used().size(), info_traversal.vars_defd().size(),
        info_traversal.inputs_used().size(),
        predicate);

    // if has input, record it
    if (!info_traversal.inputs_used().empty()) {
      this_model->AddInputPredicate(predicate);
    }
    // XXX needs fixing if it's going to "work"
    //if (!info_traversal.vars_defd_.empty() || !info_traversal.inputs_used_.empty()) {
    //  (*this_tslice)->transition_constraints.insert(predicate);
    //}
    this_model->Add(predicate);
  }
  logger.LogCloseFold(6, "");

  logger.LogOpenFold(5, "full abstract model");
  logger.LogCloseFold(5, "{}", *this_model);
  logger.Log(6, "tslice to make sure the transitions are capture:\n{}", *(*this_tslice));

  //const auto num_vars_used = influence.vars_used.size();
  //const auto num_constants_used = influence.constants_used.size();
  this_model->ExpandIntoCube(z);
  SimplifyPreimage(z);
  pimpl_->CalculateStats(z, stats_.get());
  LOG(5, "final z: {}", z);
  LOG(5, "end computing preimage");

#if !defined(NDEBUG)
  {
    //assert(!z.empty());
    // Make sure there are no next states or inputs
    for (auto& lit : z) {
      for (auto I = po_expr_iterator::begin(lit), E = po_expr_iterator::end(lit); I != E; ++I) {
        auto top = *I;
        if (FindInput(top)) {
          fmt::print(cerr, "ERROR: input in preimage\n");
          fmt::print(cerr, "offending literal: {}\n", lit);
          EUFORIA_FATAL("error");
        }
        if (top.num_args() == 0) {
          if (ends_with(top.decl().name().str(), "+")) {
            if (auto sv = FindVar(top)) {
              fmt::print(cerr, "* {} / {}\n", sv->current(), sv->next());
            }
            for (auto& sv : vars()) {
              fmt::print(cerr, "* {} / {}\n", sv.current(), sv.next());
            }
            fmt::print(cerr, "ERROR: next-state in preimage\n");
            fmt::print(cerr, "offending literal: {}", lit);
            EUFORIA_FATAL("error");
          }
          if (HasNextStateVar(top)) {
            fmt::print(cerr, "ERROR: next-state in preimage\n");
            fmt::print(cerr, "offending literal: {}\n", lit);
            EUFORIA_FATAL("error");
          }
        }
      }
    }
    for (auto& lit : z) {
      if (!is_literal_true(model->Eval(lit))) {
        fmt::print(cerr, "ERROR: literal in preimage false: {}\n", lit);
        EUFORIA_FATAL("error");
      }
    }

    for (auto& lit : z) {
      for (auto I = po_expr_iterator::begin(lit), E = po_expr_iterator::end(lit); I != E; ++I) {
        auto top = *I;
        if (top.decl().decl_kind() == Z3_OP_DISTINCT) {
          bool allConst = true;
          for (unsigned i = 0; i < top.num_args(); i++) {
            allConst = allConst && IsUConstant(top.arg(i));
          }
          assert(!allConst);
        }
      }
    }
  }
#endif


  //fmt::print(cerr, "preimg_size,num_assumps,num_constants_used,num_vars_used,partition_size: {},{},{},{},{}\n", z.size(), num_assumps, num_constants_used, num_vars_used, partition_size);
  logger.Log(5, "number of times eval() called: {}", this_model->num_evals());
  if (logger.ShouldLog(5)) {
    Statistics st;
    stringstream model_stats;
    this_model->model().collect_statistics(&st);
    st.Print(model_stats);
    logger.Log(5, "model stats:\n{}", model_stats.str());
  }
  return this_model;
}


void AbstractVmtTransitionSystem::SimplifyPreimage(Cube& z) const {
  const bool tmp_unsound_remove_arrays_preimage = false;
  if (tmp_unsound_remove_arrays_preimage) {
    for (auto itc = z.begin(); itc != z.end(); /* in body */) {
      auto literal = *itc;
      bool removed_it = false;
      for (auto it = po_expr_iterator::begin(literal),
           ie = po_expr_iterator::end(literal); it != ie; ++it) {
        auto subexpr = *it;
        // If the literal contains a SELECT call,, remove the literal from the
        // pre-image. To test how this goes on the benchmark that doesn't need
        // the arrays.
        if (subexpr.decl().decl_kind() == Z3_OP_UNINTERPRETED &&
            starts_with(subexpr.decl().name().str(), "SELECT")) {
          removed_it = true;
          itc = itc.erase();
          break;
        }
      }
      if (!removed_it) {
        ++itc;
      }
    }
  }
  return TransitionSystem::SimplifyPreimage(z);
}





void AbstractVmtTransitionSystem::AddTransitionsToChecker(Solver& LC) const {


  if (eager_constant_ordering_) {
    map<int, vector<z3::expr>> sorted_concrete_constants_by_width; // gross
    // vector<z3::expr> sorted_concrete_constants;
    // sorted_concrete_constants.reserve(absman_->constants().size());
    for (auto& abs_const : absman_->constants()) {
      auto c = Concretize(abs_const);
      sorted_concrete_constants_by_width[c.get_sort().bv_size()].push_back(c);
    }
    // sort constants by size and by GT relation, so that GT(i, i+1)
    struct scmp_const {
      const AbstractVmtTransitionSystem& axsys;
      scmp_const(const AbstractVmtTransitionSystem& axsys) : axsys(axsys) {}
      bool operator()(const z3::expr& a, const z3::expr& b) {
        auto ca = axsys.Concretize(a), cb = axsys.Concretize(b);
        const auto wa = ca.get_sort().bv_size(), wb = cb.get_sort().bv_size();
        if (wa == wb) {
          return is_literal_true((ca < cb).simplify());
        } else if (wa < wb) {
          return true;
        } else {
          return false;
        }
      }
    } signed_cmp(*this);

    struct ucmp_const {
      const AbstractVmtTransitionSystem& axsys;
      ucmp_const(const AbstractVmtTransitionSystem& axsys) : axsys(axsys) {}
      bool operator()(const z3::expr& ca, const z3::expr& cb) {
        // auto ca = axsys.Concretize(a), cb = axsys.Concretize(b);
        const auto wa = ca.get_sort().bv_size(), wb = cb.get_sort().bv_size();
        if (wa == wb) {
          return is_literal_true(z3::ult(ca, cb).simplify());
        } else if (wa < wb) {
          return true;
        } else {
          return false;
        }
      }
    } unsigned_cmp(*this);

    for (auto& entry : sorted_concrete_constants_by_width) {
      std::sort(begin(entry.second), end(entry.second), unsigned_cmp);
    }
    for (auto& entry : sorted_concrete_constants_by_width) {
      auto& constants = entry.second;
      for (size_t i = 0; i < constants.size(); i++) {
        for (size_t j = i+1; j < constants.size(); j++) {
          LC.Add(Abstract(z3::ult(constants[i], constants[j])));
          stats_->eager_constant_num_constraints++;
        }

        LC.Add(Abstract(!z3::ult(constants[i], constants[i])));
        stats_->eager_constant_num_constraints++;
      }
    }
  }

  if (background_) {
    LC.Add(background_);
  }
  AddDistinctConstConstraint(LC);
  AddOneHots(LC);
  if (auto eq_map = trans_equations()) {
    for (const auto& [lhs, rhs] : eq_map->get()) {
      LC.Add(static_cast<z3::expr>(lhs) == rhs);
    }
  }
  LC.Add(trans_rest());
}

void AbstractVmtTransitionSystem::AddInitialStateToChecker(Solver& solver) const {
  VmtTransitionSystem::AddInitialStateToChecker(solver);
  AddDistinctConstConstraint(solver);
}

void AbstractVmtTransitionSystem::AddOneHots(Solver& solver) const {
  VmtTransitionSystem::AddOneHots(solver);
  AddDistinctConstConstraint(solver);
}

z3::expr AbstractVmtTransitionSystem::Abstract(const z3::expr& e) const {
  auto r = (*pimpl_->normalize_)(e);
  auto abs = absman_->Abstract(r);
  //euforia_expensive_assert(z3::eq(r, concretize(abs)));
  return abs;
}


z3::expr AbstractVmtTransitionSystem::Concretize(const z3::expr& lit) const {
  auto conc = absman_->Concretize(lit);
  return conc;
}

const ExprSet& AbstractVmtTransitionSystem::constants() const {
  return absman_->constants();
}


}
}
