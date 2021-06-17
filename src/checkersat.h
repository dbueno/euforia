// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef checkersat_hpp
#define checkersat_hpp

#include <boost/iterator/function_output_iterator.hpp>
#include <bitset>

#include "checker_types.h"
#include "supp/solver.h"
#include "supp/std_supp.h"
#include "supp/z3_solver.h"


namespace euforia {
class Checker;
class Counterexample;
class TransitionSystem;
struct TSlice;
class Cube;
class TimedCube;
class AbstractModel;

enum class LemmaType { kOneStep, kForward };

struct AbstractLemmaClause {
  unsigned number;
  LemmaType ty;
  z3::expr activation; // used by CheckerSat

  explicit AbstractLemmaClause(unsigned number, LemmaType t, z3::context& ctx) 
      : number(number), ty(t), activation(ctx) {}

  z3::expr as_expr() const;

  void AddLit(z3::expr l);

  const auto& lits() const { return lits_; }
  auto lits_begin() const { return lits_.begin(); }
  auto lits_end() const { return lits_.end(); }
  size_t size() const { return lits_.size(); }

  class Inserter {
   public:
    Inserter(AbstractLemmaClause *c) : lemma_(c) {}

    void operator()(z3::expr e) { lemma_->AddLit(e); }

   private:
    AbstractLemmaClause *lemma_;
  };

  auto inserter() {
    return boost::make_function_output_iterator(Inserter(this));
  }

 private:
  OrderedExprSet lits_; // logical OR of these literals
};

std::ostream& operator<<(std::ostream&, const AbstractLemmaClause&);

/*----------------------------------------------------------------------------*/
constexpr int kFrameNull = -1;


class CheckerSat : public Solver {
 public:
  CheckerSat(Checker& chk, const TransitionSystem& ts, const char *logic);
  CheckerSat(const CheckerSat& other) = delete;
  CheckerSat& operator=(const CheckerSat&) = delete;

  virtual inline z3::context& ctx() const override { return notp_act_.ctx(); }
  
  inline const std::vector<std::shared_ptr<AbstractLemmaClause>>&
  forward_lemmas() const { return forward_lemmas_; }

  inline Solver& gbc_solver() { return *gbcsolver_; }
  inline Solver& init_solver() { return *isolver_; }
  inline Solver& isblocked_solver() { return *bsolver_; }
  
  //! Returns null if there is no bad Cube.
  std::shared_ptr<Cube> GetBadCube();
  
  //! true if blocked at c.frame
  bool IsBlocked(const TimedCube& c);

  //! true iff c intersects with I
  bool IsInitial(const Cube& c);
  
  CheckResult IsInitialSolve(const Cube& c);
  
  //! Parameters for SolveRelative
  using SolveRelativeParams = std::bitset<3>;
  
  //! If set, does not compute model & preimage cube
  static constexpr SolveRelativeParams ExtractModel{1 << 0};
  //! If set, does not include ~s in query
  static constexpr SolveRelativeParams NoInd{1 << 1};
  //! If set, does not generalize unreachable cube
  static constexpr SolveRelativeParams NoGen{1 << 2};

  //! if SAT, returns a TimedCube with kFrameNull. If ExtractModel is set,
  //! returns a preimage cube
  //! 
  //! if UNSAT, returns the blocked cube with the depth at which it is blocked
  //! 
  TimedCube SolveRelative(
      const TimedCube &c, SolveRelativeParams params = SolveRelativeParams(),
      int log_level = 5);

  //! When SolveRelative returns unsat, use the core to generalize the given
  //! cube. Returns a fresh cube guaranteed not to intersect with I
  std::shared_ptr<Cube> GeneralizeWithUnsatCore(
      const ExprSet& core, const Cube& c);

  //! add newly blocked cube to solver
  void BlockCubeInSolver(TimedCube s);
  //! Add lemma to the solver
  void AddLemmaInSolver(std::shared_ptr<AbstractLemmaClause>);
  //! Returns true if UNSAT(Lemmas & !e), i.e., Lemmas imply e
  bool is_lemma_redundant(const z3::expr& e);

  //! Adds background assertion to all solvers
  void AddBackground(z3::expr e);
  
  //! Gets literals in the "cone of influence" of the expression e, given the
  //! model. Basically literals that are a "reason" why e is will evaluate to
  //! true or false.
  std::vector<z3::expr> GetCoi(const std::shared_ptr<Model>& model, z3::expr e) const;

  void DumpQuery(const ExprSet& assumps);
  
  
  // stats
  //
  TimerDuration solve_sat_time_;
  TimerDuration solve_unsat_time_;
  TimerDuration solve_isinitial_time_;
  TimerDuration solve_isblocked_time_;
  TimerDuration generalize_with_core_time_;
  TimerDuration get_bad_cube_time_;
  
  int64_t num_solve_relative_ = 0;
  int64_t num_solve_relative_sat_ = 0;
  int64_t num_solve_relative_unsat_ = 0;
  int64_t num_isinitial_fast_ = 0;
  int64_t num_isinitial_queries_ = 0;
  int64_t num_isblocked_queries_ = 0;
  //! when the core is checked to intersect with I
  int64_t num_gen_core_tests_ = 0;
  //! when the core itself does not intersect with I
  int64_t num_gen_core_fast_ = 0;
  int64_t num_get_bad_cube_ = 0;
  int64_t num_block_cube_ = 0;

  RunningAvg cube_size_avg_;
  RunningMax max_cube_size_;
  
  
  void SanityCheckReachesNextFrame(Solver& S, ExprSet& assumps, int k);
  void SanityCheckFrames();

  // overrides for Solver
  virtual void Push() override;
  virtual void Pop() override;
  virtual void Add(const z3::expr& e) override;
  virtual CheckResult Check(const size_t n, const z3::expr* assumptions) override;
  using Solver::Check;
  virtual std::shared_ptr<Model> get_model() override;
  virtual z3::expr_vector unsat_core() override;
  virtual z3::expr_vector unsat_core_reasons() override;
  virtual z3::expr_vector assertions() const override;
  virtual std::string reason_unknown() const override;
  virtual std::ostream& Print(std::ostream&) const override;
  virtual void DumpBenchmark(
      std::ostream& os, size_t n, const z3::expr* assumptions) override;
  using Solver::DumpBenchmark;
  virtual const char *version() const override {
    return "CheckerSat";
  }

  virtual void collect_statistics(Statistics *) const override;

 private:
  friend class Checker;
  Checker& checker_; // holding me
  const TransitionSystem& xsys_;
  //! Activation literals. For each frame, a boolean variable. Same size as Checker's F
  std::vector<z3::expr> F_act_;
  z3::expr notp_act_; // activation literal for !P
  ExprSet assumps_;

  std::shared_ptr<AbstractModel> last_model_; // stored so cx can retrieve
  std::shared_ptr<TSlice> last_slice_; // stored w/ last model for easy feasibility checking

  std::unique_ptr<Z3Solver> solver_;
  //! contains F and is for doing GetBadCube (no T)
  std::unique_ptr<Solver> gbcsolver_;
  //! only contains I and is for doing isInitial query
  std::unique_ptr<Solver> isolver_;
  //! for doing isBlocked
  std::unique_ptr<Solver> bsolver_;
  //! stores lemmas_for is_lemma_redundant
  std::unique_ptr<Z3Solver> lsolver_;
  std::string logic_;
  
  ExprSet dedup_lemmas_;
  std::vector<std::shared_ptr<AbstractLemmaClause>> one_step_lemmas_;
  std::vector<std::shared_ptr<AbstractLemmaClause>> forward_lemmas_;
  void AddLemmaAssumps(z3::expr_vector& s) {
    for (auto& lemma : forward_lemmas_) {
      s.push_back(lemma->activation);
    }
    for (auto& lemma : one_step_lemmas_) {
      s.push_back(lemma->activation);
    }
  }
  
  void AddLemmaAssumps(ExprSet& s) {
    for (auto& lemma : forward_lemmas_) {
      s.insert(lemma->activation);
    }
    for (auto& lemma : one_step_lemmas_) {
      s.insert(lemma->activation);
    }
  }
};

}

template <>
struct euforia::pp::PrettyPrinter<euforia::AbstractLemmaClause> {
  euforia::pp::DocPtr operator()(const euforia::AbstractLemmaClause& l) {
    pp::DocStream os;
    os << "AbstractLemmaClause(";
    switch (l.ty) {
      case LemmaType::kForward:
        os << "kForward";
        break;
      case LemmaType::kOneStep:
        os << "kOneStep";
        break;
      default:
        ENSURE(false);
    }
    os << "): " << Pprint(l.as_expr());
    return os;
  }
};

template <>
struct fmt::formatter<euforia::AbstractLemmaClause> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), ie = ctx.end();
    ENSURE(it == ie || *it == '}');
    return it;
  }

  template <typename FormatContext>
  auto format(const euforia::AbstractLemmaClause& c, FormatContext& ctx) -> decltype(ctx.out()) {
    return format_to(ctx.out(), "{}", euforia::pp::Pprint(c));
  }
};



void mylog(const euforia::AbstractLemmaClause& c);

#endif
