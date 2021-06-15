// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

// This file shouldn't use log level lower than 5

#include "checkersat.h"

#include <boost/range/algorithm/copy.hpp>
#include <fstream>

#include "abstract_model.h"
#include "checker.h"
#include "cube.h"
#include "supp/debug.h"
#include "supp/euforia_config.h"
#include "supp/expr_iterators.h"
#include "supp/expr_normalize.h"
#include "supp/z3_solver.h"
#include "xsys/influence_traversal.h"

using namespace std;

namespace euforia {


z3::expr AbstractLemmaClause::as_expr() const {
  assert(!lits_.empty());
  const z3::expr& b = *lits_.begin();
  return expr_mk_or(b.ctx(), lits());
}

void AbstractLemmaClause::AddLit(z3::expr l) {
  if (euforia_config.sort_cubes) {
    ExprNormalize norm;
    l = norm(l);
  }
  lits_.emplace(l);
}
  
std::ostream& operator<<(std::ostream& os, const AbstractLemmaClause& l) {
  os << "AbstractLemmaClause(";
  switch (l.ty) {
    case LemmaType::kForward:
     os << "kForward";
     break;
    case LemmaType::kOneStep:
     os << "kOneStep";
     break;
    default:
     assert(false);
  }
  os << "): " << l.as_expr();
  //bool first = true;
  //for (auto& lit : l.lits) {
  //  if (!first) os << " || ";
  //  os << lit << endl;
  //  first = false;
  //}
  return os;
}

// Have to define storage for these outside...
constexpr CheckerSat::SolveRelativeParams CheckerSat::ExtractModel;
constexpr CheckerSat::SolveRelativeParams CheckerSat::NoInd;
constexpr CheckerSat::SolveRelativeParams CheckerSat::NoGen;


enum class IsInitialResult { IN, OUT, MAYBE };
std::ostream& operator<<(std::ostream& os, const IsInitialResult& r) {
  switch (r) {
    case IsInitialResult::IN:
      os << "IN";
      break;
    case IsInitialResult::OUT:
      os << "OUT";
      break;
    case IsInitialResult::MAYBE:
      os << "MAYBE";
      break;
  }
  return os;
}
static IsInitialResult isInitialFast(const TransitionSystem& TS, const z3::expr& e);
static bool isMaybeInitial(const TransitionSystem& TS, const z3::expr& e) {
  auto r = isInitialFast(TS, e);
  return !(r == IsInitialResult::OUT);
}


/*-----------------------------------------------------------------------------------*/

CheckerSat::CheckerSat(Checker &chk, const TransitionSystem &ts,
                       const char *logic)
    : checker_(chk), xsys_(ts),
      notp_act_(FreshBool(ts.ctx(), "boolP")), solve_sat_time_(0),
      solve_unsat_time_(0), solve_isinitial_time_(0), solve_isblocked_time_(0),
      generalize_with_core_time_(0), max_cube_size_(0), get_bad_cube_time_(0),
      logic_(logic) {
  auto make_solver = [&]() {
    if (euforia_config.no_abstract_arrays) {
      z3::solver s = (z3::tactic(ctx(), "simplify") &
                      z3::tactic(ctx(), "solve-eqs") &
                      z3::tactic(ctx(), "qfaufbv")).mk_solver();
      z3::params p(ctx());
      p.set("relevancy", 0U);
      s.set(p);
      return make_unique<Z3Solver>(s);
    } else {
      return make_unique<Z3Solver>(ctx(), logic);
    }
  };
  solver_ = make_solver();
  solver_->Push();
  solver_->Pop();
  isolver_ = make_solver();
  gbcsolver_ = make_solver();
  gbcsolver_->Push();
  gbcsolver_->Pop();
  bsolver_ = make_solver();
  bsolver_->Push();
  bsolver_->Pop();
}
  

void CheckerSat::DumpQuery(const ExprSet& assumps) {
  if (LOG_DIR.empty() || !euforia_config.dump_abstract_queries)
    return;

  ofstream outfile(fmt::format("{}/SolveRelative{:05}.smt2", LOG_DIR,
                               num_solve_relative_));
  auto smt2_formula = ToSmt2WithAssumps(assertions(), assumps, "Query", logic_);
  fmt::print(outfile, smt2_formula);
}



TimedCube CheckerSat::SolveRelative(const TimedCube& s,
                                    SolveRelativeParams params, int log_level) {
  TimedCube ret(kFrameNull);
  const unsigned k = static_cast<unsigned>(s.frame);
  assumps_.clear();
  ClearTracked();
  logger.Log(log_level, "[onestep {}] s+@F{}: {}",
             checker_.stats_.num_backward_reach,
             s.frame, *s.thecube);
  
  num_solve_relative_++;
  
  // Disable P, all we care about is s
  assumps_.insert(!notp_act_);

  // Enable lemmas
  AddLemmaAssumps(assumps_);
  
  // R[k-1] cubes are in solver, just assume them
  for (size_t i = 0; i < F_act_.size(); i++) {
    // if in R_k-1,  enable else disable
    assumps_.insert(k-1 <= i ? F_act_[i] : !F_act_[i]);
  }
  
  Push(); // so we can pop s & s+
  // ~s
  if (!(params & CheckerSat::NoInd).any()) {
    Add(s.thecube->negation());
  }

  // s+
  for (auto it = s.thecube->nbegin(), ie = s.thecube->nend(); it != ie; ++it) {
    auto b = TrackAssertion(*it, "a");
    assumps_.insert(b);
  }
  
  while (true) {
    ScopedTimeKeeper t(&solve_sat_time_); // default
    DumpQuery(assumps_);
    auto r = Check(assumps_);
#ifndef NDEBUG
    if (r == CheckResult::kUnknown)
      cerr << reason_unknown() << endl;
#endif
    assert(r == CheckResult::kSat || r == CheckResult::kUnsat);
    
    if (r == CheckResult::kSat) {
      auto dur = t.Get();
      nlogger.Log("queries", "sat {} s", dur.count());
      ++num_solve_relative_sat_;
      logger.Log(log_level, "[{}] {}R[{}] & T & s+ is SAT", num_solve_relative_,
                 (!(params & CheckerSat::NoInd).any() ? "!s & " : ""), k-1);
      if ((params & CheckerSat::ExtractModel).any()) {
        ret.thecube = std::make_unique<Cube>(ctx());
        auto model = get_model();
        last_model_ = xsys_.ExpandedPreimage(*this, model, *s.thecube,
                                             *ret.thecube, &last_slice_);
      }
      break;
      
    } else {
      auto dur = t.Get();
      nlogger.Log("queries", "unsat {} s", dur.count());
      ++num_solve_relative_unsat_;
      t.SetDurationOut(&solve_unsat_time_);
      logger.Log(log_level, "[{}] {}R[{}] & T & s+ is UNSAT", num_solve_relative_,
                 (!(params & CheckerSat::NoInd).any() ? "!s & " : ""), k-1);
      if ((params & CheckerSat::NoGen).any()) {
        ret = s;
      } else {
        z3::expr_vector core = unsat_core();
        if (core.empty()) {
          fmt::print("core is empty (T inconsistent? cores disabled?)\n");
          exit(1);
        }
        ExprSet core_set(core.begin(), core.end());
        nlogger.Log("generalize", "unsat core reduction: {} -> {} literals",
                   assumps_.size(), core_set.size());


#ifndef NO_GEN_WITH_UNSAT_CORE
        auto new_cube = GeneralizeWithUnsatCore(core_set, *s.thecube);
#endif
        
        logger.Log(6, "    new s: {}", *new_cube);
        for (int i = k-1; i <= checker_.depth(); i++) {
          if (core_set.find(F_act_[i]) != core_set.end()) {
            ret = TimedCube(new_cube, min(i+1, checker_.depth()));
            break;
          }
        }
        
        if (ret.frame == kFrameNull) {
          ret = TimedCube(new_cube, checker_.frame_inf());
        }
        assert(ret.thecube);
        assert(ret.frame != kFrameNull);
      }
      break;
    }
  }


  Pop();
  assert(!(params & CheckerSat::ExtractModel).any() || ret.thecube);
  assert(!ret.thecube || ret.frame <= checker_.frame_inf() /* for FrameInf */);
  
  if (ret.thecube && euforia_config.sort_cubes) {
    ret.thecube->sort();
  }

  if (ret.thecube) {
    cube_size_avg_ += ret.thecube->size();
    nlogger.Log("queries", "target_cube_size: {}", s.thecube->size());
    nlogger.Log("queries", "cube_size: {}", ret.thecube->size());
    auto prev_max = max_cube_size_.get();
    max_cube_size_ += static_cast<int64_t>(ret.thecube->size());
    if (prev_max < max_cube_size_.get()) {
      nlogger.Log("queries", "max_cube_size: {}", max_cube_size_.get());
    }
  }

  return ret;
}


shared_ptr<Cube> CheckerSat::GeneralizeWithUnsatCore(const ExprSet& core_set,
                                                     const Cube& c) {
  auto new_cube = make_shared<Cube>(c);
  logger.Log(6, "    core: {}", unsat_core_reasons());
  if (new_cube->size() > 1) {
    ScopedTimeKeeper t(&generalize_with_core_time_);
    auto& cuberef = *new_cube;
    Cube core_cube(c.ctx());
    // This loop makes a cube just out of the core literals. If we get
    // lucky, then that cube is both quite small and doesn't intersect
    // with I -- avoiding an expensive minimization step.
    for (int64_t i = 0; i < static_cast<int64_t>(cuberef.size()); i++) {
      const auto& elt = cuberef[i];
      auto b = GetWithDefault(tracking_bools_, cuberef.getNext(elt),
                              cuberef.getNext(elt)); // Bools hit default
      if (core_set.find(b) != core_set.end()) {
        core_cube.push(elt, cuberef.getNext(elt));
      }
    }
    ++num_gen_core_tests_;
    if (!IsInitial(core_cube)) {
      logger.Log(5, "able to use core cube immediately");
      new_cube = make_shared<Cube>(move(core_cube));
      ++num_gen_core_fast_;
    } else {
      // This tries to start with the current cube and whittle it down
      // with the core. It is especially slow when the cubhe is large
      // relative to the core size.
      for (int64_t i = 0; i < static_cast<int64_t>(cuberef.size()); ) {
        auto elt = cuberef[i];
        auto b = GetWithDefault(tracking_bools_, cuberef.getNext(elt),
                                cuberef.getNext(elt)); // Bools hit default
        if (core_set.find(b) == core_set.end()) {
          auto elt_next = cuberef.getNext(elt);
          swap(cuberef[i], cuberef[cuberef.size()-1]);
          cuberef.erase(cuberef.size()-1);
          ++num_gen_core_tests_;
          if (!IsInitial(cuberef)) {
            // Don't increment i here because we deleted an element from
            // cuberef and put a new one at place i.
            continue;
          }
          cuberef.push(elt, elt_next);
        }
        i++;
      }
      EUFORIA_EXPENSIVE_ASSERT(!IsInitial(cuberef), "cube is in I");
    }
  }
  return new_cube;
}




// XXX this method can be removed, it's only used in one place
vector<z3::expr> CheckerSat::GetCoi(const std::shared_ptr<Model>& model, z3::expr g) const {
  AbstractModel AM(model, xsys_);
  ExprSet lits; // used for returning
  auto eval = [&](const z3::expr& e, bool c) { return AM.Eval(e, c); };
  InfluenceTraversal influence(xsys_, eval, &lits);
  assert(g.is_bool());
  influence(ExprSet({g}));
#ifdef LOGGER_ON
  for (auto& lit : lits) {
    logger.Log(5, "GetCoi lit {}", lit);
  }
#endif
  
  vector<z3::expr> ret(begin(lits), end(lits));
  return ret;
}



static IsInitialResult isInitialFast(const TransitionSystem& TS, const z3::expr& e) {
  auto isZero = [](const z3::expr& e) {
    if (IsUConstant(e)) {
      auto name = e.decl().name().str();
      return ends_with(name, "_0");
    }
    return false;
  };
  auto svEqualsZero = [&TS,isZero](const z3::expr& l, const z3::expr& r) {
    return TS.FindVar(l) && isZero(r);
  };
  
  switch (e.decl().decl_kind()) {
    case Z3_OP_EQ: {
      // if e is (StateVar = 0), then it's definitely initial
      assert(e.num_args() == 2);
      auto l = e.arg(0), r = e.arg(1);
      auto inI = svEqualsZero(l,r) || svEqualsZero(r,l);
      if (inI)
        return IsInitialResult::IN;
      break;
    }
      
    case Z3_OP_DISTINCT: {
      // (distinct v ... 0) means outside I
      bool hasZero = false;
      bool hasVar = false;
      const int n = e.num_args();
      for (int i = 0; i < n; i++) {
        if (isZero(e.arg(i))) { hasZero = true; }
        if (TS.FindVar(e.arg(i))) { hasVar = true; }
      }
      if (hasVar && hasZero)
        return IsInitialResult::OUT;
    }

    default: ;
  }

  return IsInitialResult::MAYBE;
}


CheckResult CheckerSat::IsInitialSolve(const Cube& s) {
  ScopedTimeKeeper t(&solve_isinitial_time_);
  ++num_isinitial_queries_;
  init_solver().Push();
  for (auto lit : s) {
    init_solver().Add(lit);
  }
  auto result = init_solver().Check();
  init_solver().Pop();
  return result;
}


bool CheckerSat::IsInitial(const Cube& s) {
  // XXX idea: if I subsumes the this cube, it's initial
#if 0 // didn't get any hits
  if (s.empty()) {
    ++num_isinitial_fast_;
    return true;
  }
  if (all_of(ExprConjunctIterator::begin(xsys_.init_state()),
             ExprConjunctIterator::end(),
             [&](auto&& l) { return s.contains(l); })) {
    ++num_isinitial_fast_;
    return true;
  }
#endif
  // Fast syntactic check
#if 0
  for (auto& lit : s) {
    if (!isMaybeInitial(ts, lit)) {
      euforia_expensive_assert(z3::unsat == isInitialSolve(s));
      return false;
    }
  }
#endif
  
  return CheckResult::kSat == IsInitialSolve(s);
}
  
  

  
bool CheckerSat::IsBlocked(const TimedCube &s) {
  ScopedTimeKeeper t(&solve_isblocked_time_);
  ++num_isblocked_queries_;
  vector<z3::expr> assumps;
  assumps.reserve(F_act_.size());
  for (size_t i = 0; i < F_act_.size(); i++) {
    if (i >= static_cast<unsigned>(s.frame))
      assumps.push_back(F_act_[i]);
    else
      assumps.push_back(!F_act_[i]);
  }
  
  // normal check
  isblocked_solver().Push();
  for (auto& lit : *s.thecube)
    isblocked_solver().Add(lit);
  auto result = isblocked_solver().Check(assumps);
  if (result == CheckResult::kUnsat && logger.ShouldLog(6)) {
    auto reasons = isblocked_solver().unsat_core_reasons();
    logger.Log(6, "isBlocked core: {}", reasons);
  }
  isblocked_solver().Pop();
  return (result == CheckResult::kUnsat);
}
  
  
void CheckerSat::BlockCubeInSolver(TimedCube s) {
  ++num_block_cube_;
  logger.Log(5, "    (adding blocking clause {} to F{})", s.thecube->negation(), s.frame);
  auto formula = s.thecube->negation();
  solver_->Add(!F_act_[s.frame] || formula);
  gbc_solver().Add(!F_act_[s.frame] || formula);
  isblocked_solver().Add(!F_act_[s.frame] || formula);
#ifdef EXPENSIVECHECKS
  SanityCheckFrames();
#endif
}

void CheckerSat::AddLemmaInSolver(shared_ptr<AbstractLemmaClause> lemma) {
  // XXX if lemma is only on next-state vars then it can be skipped from being added to isolver_
  // XXX same for bsolver_
  auto e = lemma->as_expr();
  ExprNormalize normalize;
  auto e_normal = normalize(e);
  auto is_irredundant = dedup_lemmas_.insert(e_normal).second;
  // Ignores redundant lemmas. They can be generated when mining all the states
  // of a counterexample for lemmas.
  if (!is_irredundant)
    return;

  switch (lemma->ty) {
    case LemmaType::kOneStep:
      one_step_lemmas_.push_back(lemma);
      break;
    case LemmaType::kForward:
      forward_lemmas_.push_back(lemma);
      break;
  }
  string label = "activate_lemma" + to_string(lemma->number);
  lemma->activation = FreshBool(ctx(), label.c_str());
  solver_->Add(!lemma->activation || e);
  gbc_solver().Add(e);
  isblocked_solver().Add(e);
  init_solver().Add(e);
  if (lsolver_) {
    lsolver_->Add(e);
  }
}

bool CheckerSat::is_lemma_redundant(const z3::expr& lemma) {
  bool redundant = false;
  if (!lsolver_) {
    lsolver_ = make_unique<Z3Solver>(ctx(), "QF_UF");
  }
  lsolver_->Push();
  lsolver_->Add(!lemma);
  if (lsolver_->Check() == CheckResult::kUnsat) {
    redundant = true;
  }
  lsolver_->Pop();
  return redundant;
}


void CheckerSat::AddBackground(z3::expr e) {
  if (is_literal_true(e))
    return;
  solver_->Add(e);
  gbc_solver().Add(e);
  isblocked_solver().Add(e);
  init_solver().Add(e);
  if (lsolver_) {
    lsolver_->Add(e);
  }
}
  
  
shared_ptr<Cube> CheckerSat::GetBadCube() {
  ++num_get_bad_cube_;
  logger.Log(5, "\n\n[find !P]");
  shared_ptr<Cube> c;
  z3::expr_vector assumps(ctx());
  for (size_t i = checker_.depth(); i < checker_.F.size(); i++) {
    assumps.push_back(F_act_[i]);
  }
  CheckResult result;
  {
    ScopedTimeKeeper t(&get_bad_cube_time_);
    result = gbc_solver().Check(assumps);
  }
  if (result == CheckResult::kUnsat) {
    logger.Log(5, "R[{}] & !P is UNSAT", checker_.depth());
    return c;
  }
  logger.Log(5, "R[{}] & !P is SAT", checker_.depth());

  // Grab the model and push all the new literals onto the Cube.
  c = std::make_unique<Cube>(ctx());
  auto model = gbc_solver().get_model();

  for (auto lit : GetCoi(model, expr_not(xsys_.property()))) {
    c->push(lit, checker_.xsys_.prime(lit));
  }
  if (euforia_config.sort_cubes) {
    c->sort();
  }

  return c;
}


void CheckerSat::SanityCheckReachesNextFrame(Solver& S, ExprSet& assumps, int k) {
  // !R_i+1
  vector<pair<z3::expr, int>> negation_R_inext;
  for (size_t i = k+1; i < checker_.F.size(); i++) {
    for (auto& cube : checker_.F[i]) {
      negation_R_inext.push_back(make_pair(cube->asExprNext(), i));
    }
  }
  z3::expr negation_R_inext_or = ctx().bool_val(false);
  for (const auto& [cube, i] : negation_R_inext) {
    (void)i;
    negation_R_inext_or = expr_or(negation_R_inext_or, cube);
  }
  string label = fmt::format("!R_{}+", k+1);
  auto negation_r_inext_tracker = S.TrackAssertion(negation_R_inext_or, label.c_str());
  assumps.insert(negation_r_inext_tracker);
  if (is_literal_false(negation_r_inext_tracker))
    return;
  logger.Log(4, "assertions for SanityCheckFrames: {}", S.assertions());
  logger.Log(4, "assumps: {}", assumps);
  auto result = S.Check(assumps);
  if (result == CheckResult::kSat) {
    fmt::print(cerr, "assertions:\n{}", S.assertions());
    auto model = S.get_model();
    fmt::print(cerr, "model:\n{}", *model);
    checker_.PrintState(0);
    fmt::print(cerr, "R_{} & T reaches outside R_{}+, at depth {} (bad)\n", k, k+1, checker_.depth());
    fmt::print(cerr, "R_{}:\n", k);
    for (size_t i = k; i < checker_.F.size(); i++) {
      for (auto& cube : checker_.F[i]) {
        fmt::print(cerr, "{}\n", cube->negation()); ///, cube->asExpr());
      }
    }
    
    auto cx_model = xsys_.GetModel(model);
    fmt::print(cerr, "using this Counterexample model {}\n", *cx_model);
    for (const auto& [cube, i] : negation_R_inext) {
      if (is_literal_true(model->Eval(cube))) {
        fmt::print(cerr, "cube from F_{} is reachable: {}\n", i, cube);
      }
    }
    EUFORIA_FATAL("error");
  } else {
    auto core = S.unsat_core();
    logger.Log(4, "SanityCheckFrames core: {}", core);
  }
  assert(result == CheckResult::kUnsat);
  logger.Log(4, "SanityCheckFrames R_{} & T correctly must reach R_{}+, at depth {}", k, k+1, checker_.depth());
}

void CheckerSat::SanityCheckFrames() {
  logger.LogOpenFold(4, "SanityCheckFrames begin");
  // ensure R_1 is satisfiable
  for (size_t k = 1; k < checker_.F.size()-2; k++) {
    ExprSet assumps;
    AddLemmaAssumps(assumps);
    for (size_t i = 0; i < checker_.F.size(); i++) {
      // part of Rk
      assumps.insert(k-1 <= i ? F_act_[i] : !F_act_[i]);
    }
    auto r = Check(assumps);
    if (r == CheckResult::kUnsat) {
      checker_.PrintState(0);
      checker_.PrintAssertions();
      fmt::print(cerr, "R_{} is UNSAT\n", k);
      auto reasons = unsat_core_reasons();
      cerr << reasons << endl;
      EUFORIA_FATAL("SanityCheckFrames failed");
    }
    logger.Log(4, "SanityCheckFrames R_{} is satisfiable (good)", k);
  }

  
  // check initial state reaching R_1
  {
    logger.Log(4, "SanityCheckFrames checking initial state -> R_1");
    ExprSet assumps;
    Z3Solver S(ctx(), logic_.c_str());
    xsys_.AddTransitionsToChecker(S);
    for (const auto& lemma : one_step_lemmas_) {
      assumps.insert(S.TrackAssertion(lemma->as_expr(), "onestep"));
    }
    for (const auto& lemma : forward_lemmas_) {
      assumps.insert(S.TrackAssertion(lemma->as_expr(), "fwd"));
    }
    xsys_.AddInitialStateToChecker(S);
    SanityCheckReachesNextFrame(S, assumps, 0);
  }


  // check rest of over-approximations
  //ensure R_i+1 is an over-approx of image of R_i
  for (int k = 1; k < checker_.depth(); k++) {
    logger.Log(4, "SanityCheckFrames checking R_{} -> R_{}", k, k+1);
    ExprSet assumps;
    Z3Solver S(ctx(), logic_.c_str());
    xsys_.AddTransitionsToChecker(S);
    for (const auto& lemma : one_step_lemmas_) {
      assumps.insert(S.TrackAssertion(lemma->as_expr(), "onestep"));
    }
    for (const auto& lemma : forward_lemmas_) {
      assumps.insert(S.TrackAssertion(lemma->as_expr(), "fwd"));
    }
    // R_i
    for (size_t i = k; i < checker_.F.size(); i++) {
      for (auto& cube : checker_.F[i]) {
        string label = fmt::format("R_{}", k);
        assumps.insert(S.TrackAssertion(cube->negation(), label.c_str()));
      }
    }
    SanityCheckReachesNextFrame(S, assumps, k);
  }

  logger.LogCloseFold(4, "SanityCheckFrames end");
}

void CheckerSat::Push() { solver_->Push(); }
void CheckerSat::Pop() { solver_->Pop(); }
void CheckerSat::Add(const z3::expr& e) { solver_->Add(e); }
CheckResult CheckerSat::Check(const size_t n, const z3::expr* assumptions) {
  return solver_->Check(n, assumptions);
}
std::shared_ptr<Model> CheckerSat::get_model() { return solver_->get_model(); }
z3::expr_vector CheckerSat::unsat_core() { return solver_->unsat_core(); }
z3::expr_vector CheckerSat::unsat_core_reasons() {
  return solver_->unsat_core_reasons();
}
z3::expr_vector CheckerSat::assertions() const { return solver_->assertions(); }
std::string CheckerSat::reason_unknown() const {
  return solver_->reason_unknown();
}
std::ostream& CheckerSat::Print(std::ostream& os) const {
  return solver_->Print(os);
}

void CheckerSat::DumpBenchmark(
    std::ostream& os, size_t n, const z3::expr* assumptions) {
  return solver_->DumpBenchmark(os, n, assumptions);
}

void CheckerSat::collect_statistics(Statistics *st) const {
  Solver::collect_statistics(st);
  gbcsolver_->collect_statistics(st);
  isolver_->collect_statistics(st);
  bsolver_->collect_statistics(st);
  if (lsolver_) { lsolver_->collect_statistics(st); }
}

void mylog(const euforia::AbstractLemmaClause& c) {
  cerr << c << endl;
}

}
