// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_ABSTRACT_CHECKER_IMPL_H_
#define EUFORIA_ABSTRACT_CHECKER_IMPL_H_

#include "abstract_checker.h"
#include "refinement/layered_refinement.h"
#include "refinement/symex.h"
#include "supp/boolector_solver.h"
#include "supp/euforia_config.h"
#include "supp/z3_solver.h"
#include "xsys/abstract_vmt_transition_system.h"

namespace euforia {

using namespace std;
using namespace boolector;
using namespace llvm;
using namespace euforia::vmt;

extern int kBtorLogLevel;

// Define this to turn on Boolector logging by defining the macros below. You
// have to compile Boolector in debug mode first with configure -g
#ifdef ENABLE_BTOR_LOG

// Temporary logging to see if I can find commonalities in Boolector lemmas
// across queries.
#define BTOR_LOG_UP(log_level)  {\
  solver_.btor_solver()->setOption(BTOR_OPT_VERBOSITY, log_level); \
  solver_.btor_solver()->setOption(BTOR_OPT_LOGLEVEL, log_level); }

#define BTOR_LOG_DOWN() { \
  solver_.btor_solver()->PrintStats(); \
  solver_.btor_solver()->ResetStats(); \
  solver_.btor_solver()->setOption(BTOR_OPT_VERBOSITY, 0); \
  solver_.btor_solver()->setOption(BTOR_OPT_LOGLEVEL, 0); }

#else

#define BTOR_LOG_UP(...) (void)kBtorLogLevel;
#define BTOR_LOG_DOWN(...) (void)kBtorLogLevel;

#endif

class ReachabilityGraph;
class ReachStep;
struct AbstractLemmaClause;
enum class LemmaType;
class BmcSymexRefiner;

class AbstractChecker::Impl {
 public:
  TimerClock clk_;
  
  struct Stats {
    // time spent refining states
    TimerDuration refine_individual_time;
    // time spent refining steps
    TimerDuration refine_step_time;
    TimerDuration refine_forward_time;
    int64_t num_forward_lemmas = 0;
    int64_t num_onestep_lemmas = 0;
    int64_t num_state_refinements = 0;
    int64_t num_step_refinements = 0;
    int64_t num_forward_refinements = 0;
    int64_t num_interpolation_refinements;
    int64_t num_lemmas_with_select;
    int64_t num_lemmas_with_store;
    int64_t num_lemmas_with_bvnum;
    int64_t num_lemmas_with_array_ops;
    int64_t num_lemmas_with_const_array;
    int64_t num_refinement_queries = 0;
    // # of concrete queries that contain arrays (because this is essentially
    // what we're trying to minimize)
    int64_t num_concrete_array_queries = 0;
    int64_t num_layered_queries = 0;
    // # spurious layered abstractions (layered abstraction did noting)
    int64_t num_layered_spurious_queries = 0;

    void Reset() {
      (*this) = {};
    }
  };

  Stats stats_;

  Impl(const ConcreteVmtTransitionSystem& C, AbstractVmtTransitionSystem& A,
       AbstractChecker& parent);
  Impl(const AbstractChecker&) = delete;
  ~Impl();

  inline z3::context& ctx() const { return cxsys_.ctx(); }
  inline Solver& solver() const { return *solver_; }

  // refinement entry point
  std::unique_ptr<Counterexample> 
  RefineFromAcx(const ReachabilityGraph& g);

  shared_ptr<AbstractLemmaClause> MakeLemma(LemmaType ty);
  
  shared_ptr<AbstractLemmaClause> LearnLemmas(const z3::expr& abs_mus,
                                              const string& where);

  // returns true if lemma was learned, false if duplicate
  bool LearnLemmaInSolver(const std::shared_ptr<AbstractLemmaClause>&,
                          const std::string& where);

  // given an MUS, canonicalize and learn from it
  shared_ptr<AbstractLemmaClause> RefineWithCore(
      const ExprSet& mus, LemmaType ty, const std::string& where);

  shared_ptr<AbstractLemmaClause> RefineExistentially(
      const symex::State& prev_state, const ExprSet& inpredicates,
      const TSlice&, const ExprSet& MUS, LemmaType ty,
      const std::string& where, const ExprSet *inputConsts = nullptr);

  void ValidateStateLemma(const AbstractLemmaClause& lemma,
                          const ReachStep& step);
  void ValidateLemma(const AbstractLemmaClause& lemma,
                     const z3::expr& state_acx);
  void CheckEufInvalidity(const AbstractLemmaClause& lemma);
  
  bool RefineStates(const ReachabilityGraph&);
  bool RefineSteps(const ReachabilityGraph&);
  std::unique_ptr<Counterexample>
  RefineWithBmc(const ReachabilityGraph&);
  std::unique_ptr<BoolectorCounterexample>
  RefineWithBmcSpacer(const ReachabilityGraph&);
  std::unique_ptr<Counterexample>
  RefineWithBmcOneShot(const ReachabilityGraph& reached);
  
  shared_ptr<symex::State> CheckInitialState(
      symex::Executor& symex, const ReachabilityGraph& reached);

  z3::expr GeneralizeMus(const ExprSet&);

  static constexpr bool kUseTSlice = false;
  boost::optional<ExprSet> trans_constraints_;
  const ExprSet TSliceTransitionConstraints(const TSlice&);

  //! Makes a BoolectorSolver with settings (model generation and
  //! incrementality) and assertions appropriate for refinement queries
  //! (background assertion from concrete sys)
  unique_ptr<BoolectorSolver> MakeBoolectorSolver() const;

  unique_ptr<Z3Solver> MakeZ3Solver() const;

  unique_ptr<Solver> make_solver() const;

  AbstractVmtTransitionSystem& axsys() { return axsys_; }
  const ConcreteVmtTransitionSystem& cxsys() const { return cxsys_; }

  const auto& recent_lemmas() const { return recent_lemmas_; }

  void collect_statistics(Statistics *st) const;

 private:
  const ConcreteVmtTransitionSystem& cxsys_;
  AbstractVmtTransitionSystem& axsys_;
  vector<shared_ptr<AbstractLemmaClause>> recent_lemmas_;
  bool refine_states_ = true;
  bool multiple_ = true;
  shared_ptr<EufBvSolver::LayeredAbstraction> layered_abstractor_;
  unique_ptr<BmcSymexRefiner> symex_refine_;
  
  void CharacterizeMus(const z3::expr& mus_expr);

 public:
  // contains boolector instance, for refinement
  // must be initialized after cxsys_
  shared_ptr<Solver> solver_;
  Checker *achk_;
  AbstractChecker& parent_;
};

} // end namespace euforia

#endif
