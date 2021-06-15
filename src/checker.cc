// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "checker.h"

#include <boost/algorithm/cxx11/all_of.hpp>
#include <boost/heap/priority_queue.hpp>
#include <queue>
#include <fstream>

#include "counterexample.h"
#include "supp/euforia_config.h"
#include "supp/expr_supp.h"
#include "supp/reachability_graph.h"
#include "supp/std_supp.h"
#include "supp/z3_solver.h"


using namespace std;


/*-----------------------------------------------------------------------------------*/

// if this is true, then produces query times in an easily grep-able and precise format
// false means a human wants to look at the trace
#ifdef OLD_TIMING_CODE
static constexpr bool traceQueryTimes = true;
#endif

/*-----------------------------------------------------------------------------------*/

// we want the earlier frames to come before later ones in the queue
namespace std {
template <>
struct less<euforia::TimedCube> {
  inline bool operator()(const euforia::TimedCube& lhs,
                         const euforia::TimedCube& rhs) const {
    return lhs.frame > rhs.frame;
  }
};
}


/*-----------------------------------------------------------------------------------*/


namespace euforia {


// Queue for backward reachability. Always pops lowest frame first.
// using tcube_queue = priority_queue<TimedCube, vector<TimedCube>, std::less<TimedCube>>;
using tcube_queue =
    boost::heap::priority_queue<TimedCube, boost::heap::stable<true>>;



//// CHECKER

Checker::Checker(const TransitionSystem& ts) 
    : xsys_(ts),
    solver_(std::make_unique<CheckerSat>(*this, ts, ts.solver_logic())),
    reach_graph_(nullptr), invariant_frame_(-1),
    runID(0) {
  logger.Log(2, "Checker setting solver logic to {}", ts.solver_logic());
  assert(ts.solver_logic());
//    auto pattern = LOG_PREAMBLE + "[" + to_string(runID) + "_" + to_string(num_backward_reach_) + "]: %v";
//    log->set_pattern(pattern);
//    lowlog->set_pattern(pattern);
}

Checker::~Checker() = default;


void Checker::PrintState(int log_level) const {
  if (!logger.ShouldLog(log_level)) {
    return;
  }

  for (int i = 0; i <= depth(); i++) {
    auto& frame = F[i];
    stringstream fs;
    bool first = true;
    for (const auto& cube : frame) {
      fs << (first ? "" : ", ");
      fs << *cube;
      if (first) first = false;
    }
    auto extra = "";
//#ifdef DIRTYBIT
//      extra = D[i] ? "*" : "";
//#endif
    logger.Log(log_level, "  > {}F{} [{}]: {}", extra, i, frame.size(), fs.str());

  }
  stringstream Finf;
  bool first = true;
  for (const auto& cube : F[frame_inf()]) {
    Finf << (first ? "" : ", ");
    Finf << *cube;
    if (first) first = false;
  }
  auto extra = "";
//#ifdef DIRTYBIT
//    extra =  D[D.size()-1] ? "*" : "";
//#endif
  logger.Log(log_level, "  > {}Finf [{}]: {}", extra, F[frame_inf()].size(), Finf.str());
}

void Checker::collect_statistics(Statistics *st) const {
  solver_->collect_statistics(st);
#define PRINT_STAT(stat, description) \
  st->Update(#stat, stats_.stat)
#define PRINT_solver_STAT(stat, description) \
  st->Update(#stat, solver_->stat ## _)
  st->Update("depth", static_cast<int64_t>(depth()));
  st->Update("num_one_step_queries", solver_->num_solve_relative_);
  PRINT_solver_STAT(num_solve_relative_sat, " - one step sat");
  PRINT_solver_STAT(num_solve_relative_unsat, " - one step unsat");
  PRINT_solver_STAT(num_gen_core_tests, " - num times (unsat-cube & I) is tesed");
  PRINT_solver_STAT(num_gen_core_fast, " - num times (unsat-cube[core] & I) is unsat");
  int64_t sum = 0;
  sum += stats_.num_cti_queries;
  PRINT_STAT(num_cti_queries, "CTI queries");
  sum += stats_.num_mus_queries;
  PRINT_STAT(num_mus_queries, "mus queries");
  sum += stats_.num_propagate_queries;
  PRINT_STAT(num_propagate_queries, "queries for forward prop");
  sum += stats_.num_pic_queries;
  PRINT_STAT(num_pic_queries, "push-inner-cube queries");
  PRINT_solver_STAT(num_get_bad_cube, " - queries of !P at depth");
  PRINT_STAT(num_backward_reach, " - number of proof obligations processed during reachability");
  PRINT_STAT(num_subsumption_blocked, " - num times subsumption blocked");
  PRINT_solver_STAT(num_isinitial_queries, " - solver queries to test (cube & I)");
  PRINT_solver_STAT(num_isinitial_fast, " - fast answer to (cube & I)");
  PRINT_solver_STAT(num_isblocked_queries, " - solver queries to test whether cube is blocked");
  PRINT_solver_STAT(num_block_cube, " - calls to block cube");
  int64_t cx_length = 0;
  sum = 0;
  if (invariant_frame_ > -1) {
    for (size_t i = invariant_frame_; i < F.size(); i++) {
      auto& frame = F[i];
      for (auto& cube : frame) {
        sum += cube->size();
      }
    }
  } else if (reach_graph_) {
    cx_length = reach_graph_->cx_length();
  }
  st->Update("num_invariant_literals", sum); // - number of literals in invariant\n", sum);
  st->Update("num_counterexample_steps", cx_length);
  st->Update("solve_time", (solver_->solve_sat_time_+solver_->solve_unsat_time_+solver_->solve_isblocked_time_+solver_->solve_isinitial_time_).count()); // abstract solve time
#define PRINT_TIME(stat) \
  st->Update(#stat, stats_.stat.count());
#define PRINT_solver_TIME(stat) \
  st->Update(#stat, solver_->stat ## _.count());
  PRINT_solver_TIME(solve_sat_time); //: {:.6f} - one-step queries that were sat\n", solver_->solve_sat_time_.count());
  PRINT_solver_TIME(solve_unsat_time); //: {:.6f} - one-step queries that were unsat\n", solver_->solve_unsat_time_.count());
  PRINT_solver_TIME(solve_isinitial_time); //: {:.6f}\n", solver_->solve_isinitial_time_.count());
  PRINT_solver_TIME(solve_isblocked_time); //: {:.6f}\n", solver_->solve_isblocked_time_.count());
  PRINT_solver_TIME(get_bad_cube_time); //: {:.6f}\n", solver_->get_bad_cube_time_.count());
  PRINT_solver_TIME(generalize_with_core_time); //: {:.6f}\n", solver_->generalize_with_core_time_.count());
  PRINT_TIME(backward_reach_time); //: {:.6f}\n", backward_reach_time_.count());
  PRINT_TIME(forward_propagate_time); //: {:.6f}\n", forward_propagate_time_.count());
  PRINT_TIME(generalize_time); //: {:.6f} - generalizing abs. cubes\n", generalize_time_.count());
  st->Update("num_solve_calls",
             static_cast<int64_t>(solver_->num_solve_calls()+solver_->init_solver().num_solve_calls()+solver_->isblocked_solver().num_solve_calls()));
  st->Update("num_solve_sat_calls",
             static_cast<int64_t>(solver_->num_solve_sat_calls()+solver_->init_solver().num_solve_sat_calls()+solver_->isblocked_solver().num_solve_sat_calls()));
  st->Update("num_solve_unsat_calls",
             static_cast<int64_t>(solver_->num_solve_unsat_calls()+solver_->init_solver().num_solve_unsat_calls()+solver_->isblocked_solver().num_solve_unsat_calls()));
  st->Update("num_unsat_core_calls",
             static_cast<int64_t>(solver_->num_unsat_core_calls()+solver_->init_solver().num_unsat_core_calls()+solver_->isblocked_solver().num_unsat_core_calls()));
  PRINT_STAT(num_added_cubes, "");
  st->Update("max_cube_size", solver_->max_cube_size_.get());
  st->Update("avg_cube_size", solver_->cube_size_avg_.get());
  st->Update("num_refine_one_step_lemmas", static_cast<int64_t>(solver_->one_step_lemmas_.size()));
  st->Update("num_refine_forward_lemmas", static_cast<int64_t>(solver_->forward_lemmas_.size()));
  auto num_total_lemmas = solver_->one_step_lemmas_.size()+solver_->forward_lemmas_.size();
  auto fraction_one_step_lemmas = num_total_lemmas == 0 ? 0 :
      100.f*static_cast<float>(solver_->one_step_lemmas_.size())/static_cast<float>(num_total_lemmas) ;
  st->Update("fraction_one_step_lemmas", fraction_one_step_lemmas);
#undef PRINT_solver_STAT
#undef PRINT_STAT
}



/*-----------------------------------------------------------------------------------*/

void Checker::PrintAssertions() {
  logger.Log(4, "printing assertions before search");
  if (!LOG_DIR.empty()) {
    ofstream assertion_file;
    assertion_file.open(LOG_DIR + "/" + "abscheck_assertions.smt2");
    auto assertions = solver_->assertions();
    ExprSet assumps;
    fmt::print(assertion_file, "{}", ToSmt2WithAssumps(assertions, assumps,
                                                       "assertions",
                                                       xsys_.solver_logic()));
    //for (size_t i = 0; i < assertions.size(); i++) {
    //  fmt::print(assertion_file, "{}\n", assertions[i]);
    //}
  }
  if (logger.ShouldLog(4))
    solver_->Print(std::cout);
}


bool Checker::Run() {
  if (++runID == 1) {
    logger.Log(4, "initializing isolver");
    xsys_.AddInitialStateToChecker(*solver_->isolver_);
    
    logger.Log(4, "initializing bsolver");
    xsys_.AddOneHots(*solver_->bsolver_);
    solver_->bsolver_->Add(xsys_.trans_rest());
    
    logger.Log(4, "initializing main solver");
    xsys_.AddTransitionsToChecker(*solver_);
    
    F.emplace_back(vector<shared_ptr<Cube>>()); // F_infinity
#ifdef DIRTYBIT
    D.push_back(true);
#endif
    solver_->F_act_.push_back(FreshBool(ctx(), "bool_activate_Finf"));
    
    NewFrame(); // create F[0]
#ifdef DIRTYBIT
    D[0] = false; // never looked at
#endif
    solver_->Add(!solver_->F_act_[0] || xsys_.init_state());
    solver_->Add(!solver_->notp_act_ || expr_not(xsys_.property()));
    
    logger.Log(4, "initializing gbcsolver");
    solver_->gbc_solver().Add(!solver_->F_act_[0] || xsys_.init_state());
    solver_->gbc_solver().Add(expr_not(xsys_.property()));

    
    PrintAssertions();
  }

  assert(runID == 1 || (reach_graph_ && "Didn't get CX last time so don't run again"));
  assert(invariant_frame_ == -1);
  reach_graph_ = nullptr;
  FlushStagedLemmas();


  // logger.Log(1, "beginning search {}", runID);
  bool ret;
  const bool found_counterexample = true, found_invariant = false;
  while (true) {
    logger.Log(4, "frames:");
    PrintState(4);
    if (auto c = solver_->GetBadCube(); c) {
      if (BackwardReachability(TimedCube(c, depth()))) {
        ret = found_counterexample;
        break;
      }
    } else {
      NewFrame();
      if (PropagateBlockedCubes()) {
        ret = found_invariant;
        break;
      }
    }
  }
  SummarizeFrames(1);
  logger.Log(4, "final frames:");
  PrintState(4);
  return ret;
}


// Prints a compact status of the IC3 frames
void Checker::SummarizeFrames(int log_level) const {
  if (!logger.ShouldLog(log_level))
    return;
  ostringstream ss;
  for (unsigned i = 1; i < F.size(); i++) {
    ss << " ";
    if (static_cast<int>(i) == frame_inf())
      ss << "| ";
    ss << F[i].size();
  }
  ss << " | 1-step:" << solver_->one_step_lemmas_.size() << " forward:" <<
      solver_->forward_lemmas_.size();
  logger.Log(log_level, "#{} {}:{}", runID, depth(), ss.str());
}


void Checker::NewFrame() {
  const auto n = F.size();
  if (n > 2) {
    SummarizeFrames(1);
  }
  assert(n == solver_->F_act_.size());
#ifdef DIRTYBIT
  assert(n == D.size());
  D.push_back(true);
#endif
  F.emplace_back(vector<shared_ptr<Cube>>());
  std::swap(F[n], F[n-1]);
  string name = "bool_activate_F" + to_string(n-1);
  solver_->F_act_.emplace_back(FreshBool(ctx(), name.c_str()));
  std::swap(solver_->F_act_[n], solver_->F_act_[n-1]);
  if (n > 1) {
    solver_->gbc_solver().Add(!solver_->F_act_[n-2]);
  }
#if 0 // DIRTYBIT
    for (size_t i = 1; i < F.size(); i++) {
      TRACE("{}{} ", D[i] ? "*" : "", F[i].size());
    }
#endif
}


inline void Checker::DumpCx(const ReachabilityGraph& reach_graph) const {
#ifdef LOGGER_ON/*{{{*/
  if (!LOG_DIR.empty()) {
    ofstream of(LOG_DIR + "/reach" + to_string(runID) + "_cx.dot",
                std::ios::out);
    reach_graph.as_dot(of, "run " + to_string(runID)
                       + ", depth " + to_string(depth())
                       + ", num. backReach " + 
                       to_string(stats_.num_backward_reach));
    of.close();
  }
#endif/*}}}*/

}

inline void Checker::DumpReachGraph(const ReachabilityGraph& reach_graph) const {
#ifdef LOGGER_ON/*{{{*/
    if (!LOG_DIR.empty() && logger.ShouldLog(5)) {// && llvm::isa<TransitionSystem>(ts)) {
      ofstream of(LOG_DIR + "/reach" + to_string(runID) + "-depth" + 
                  to_string(depth()) + ".dot", std::ios::out);
      reach_graph.as_dot(of, "depth " + to_string(depth())
              + ", num. backReach " + to_string(stats_.num_backward_reach));
      of.close();
    }
#endif/*}}}*/
}


bool Checker::BackwardReachability(TimedCube s0) {
  ScopedTimeKeeper t(&stats_.backward_reach_time);
  static int64_t start = 0;
  static int64_t sat = 0, unsat = 0, blk = 0;
  tcube_queue Q;
  ReachabilityGraph reach_graph(depth(), stats_.num_backward_reach, xsys_); // partial, potential CX
  Q.push(s0);

  logger.Log(3, "BackwardReachability start (finished {} pobs), depth {}\n",
             stats_.num_backward_reach, depth());
  while (!Q.empty()) {
    ++start;
    stats_.num_backward_reach++;
    TimedCube s = Q.top();
    Q.pop();
    
    if (s.frame == 0) {
      DumpCx(reach_graph);
      reach_graph.SetInit(s);
      reach_graph_ = std::make_unique<ReachabilityGraph>(reach_graph);
      return true;
    }

    logger.Log(3, "[pob{}]", stats_.num_backward_reach);
    if (!IsBlocked(s)) {
      logger.Log(4, "target cube {}", stats_.num_backward_reach,
                 s.thecube->ID);
      assert(!solver_->IsInitial(*s.thecube));
      ++stats_.num_cti_queries;
      auto z = solver_->SolveRelative(s, CheckerSat::ExtractModel, 4);
      if (z.frame != kFrameNull) {
        ++unsat;
        assert(z.thecube != s.thecube); // malloc inside of SolveRelative
        logger.Log(5, "    reduced unsat cube: {} in F[{}]",
                   z.thecube->asExpr(), z.frame);
        auto zs = Generalize(z, s);
        int maxframe = -1; // max of blocked-at frames
        for (auto zgen : zs) {
          while (zgen.frame < depth()-1) {
            ++stats_.num_pic_queries;
            if (!CondAssign(zgen, solver_->SolveRelative(zgen.next())))
              break;
          }  
          reach_graph.AddUnreachable(stats_.num_backward_reach, zgen, s);
          AddBlockedCube(zgen);
          maxframe = std::max(maxframe, zgen.frame);
        }
        logger.LogCloseFold(5, "[done generalizing]");
        if (maxframe < depth() && maxframe != frame_inf()) {
          // s is blocked in genframe but it reaches bad. if it's reachable at
          // s.frame+1, we will reach bad, so try that.
          logger.Log(5, "    (enqueuing s@F{})", maxframe+1);
          Q.push(TimedCube(s.thecube, maxframe+1));
        }
      } else {
        (void)++sat;
        z.frame = s.frame-1;
        logger.Log(5, "    expanded preimage: {} in F[{}]", z.thecube->asExpr(),
                   z.frame);
        if (!(z.frame == 0 || !solver_->IsInitial(*z.thecube))) {// && "cube preimage isInitial");
          // I =/=> !s, which is due to insufficiencies in preimage having to
          // do with inputs. Rare case, but must return unknown
          fmt::print(cout, "unknown\n");
          exit(42);
        }
        assert(!IsBlocked(z) && "cube preimage is immediately blocked, which is...wrong");
        reach_graph.AddReachable(stats_.num_backward_reach, z, s,
                                 move(solver_->last_model_),
                                 move(solver_->last_slice_));
        Q.push(z);
        Q.push(s);
      }
    } else {
      blk++;
      logger.Log(5, "cube {} blocked, skipping", s.thecube->ID);
    }
    DumpReachGraph(reach_graph);
  }

  
  return false; // no cx
}




vector<TimedCube> Checker::Generalize(TimedCube z, TimedCube /*orig*/) {
  ScopedTimeKeeper timekeep(&stats_.generalize_time);
  logger.LogOpenFold(5, "[generalizing]");
  vector<TimedCube> ret;
  ret.reserve(2);
  
#ifdef GENDATA_FIRST
//    if (z.thecube->size() == 1 && ts.isControlLocation((*z.thecube)[0])) {
  
    logger.Log(5, "[gendata attempt on orig s (loc {})]", z);
#ifdef GENDATA_WITH_LOC
  if (z.thecube->size() == 1 && ts.isControlLocation((*z.thecube)[0])) {
    // mostly beneficial o remove this line
    logger.Log(5, "   adding blocked loc {}", z);
    ret.push_back(z);
  }
#endif
  
  if (orig.thecube->size() > 1) {
    // re-query on just data in orig cube
//        TimedCube t(make_shared<cube>(*orig.thecube, (*z.thecube)[0]), orig.frame);
    TimedCube t(make_shared<cube>(*orig.thecube), orig.frame);
    bool erased = false;
    for (auto it = t.thecube->begin(); it != t.thecube->end();) {
      if (ts.isControlLocation(*it)) {
        it = it.erase(); // removes @L or @W
        erased = true;
      } else ++it;
    }
    if (erased && t.thecube->size() >= 1 && !solver_->isInitial(*t.thecube)) {
      T.start();
      if (condAssign(z, solver_->SolveRelative(t))) {
        // z is now blockd data cube
        logger.Log(5, "   adding blocked data: {}", z);
      }
      T.end();
      if (traceQueryTimes && ++start % every == 0) {
        logger.Log(4, "    [gen eavg:{:.3f} ms]\n", T.avg);
      }
    }
  }
//    }
#endif

#if 0
  // explode distict in code before generalizing
  //fmt::print(cerr, "cube before explode: {}\n", z);
  bool exploded = false;
  for (size_t i = 0; i < z.thecube->size(); ) {
    auto lit = (*z.thecube)[i];
    if (is_distinct(lit) && lit.num_args() > 2) {
      exploded = true;
      for (int j = 0; j < lit.num_args(); j++) {
        for (int k = j+1; k < lit.num_args(); k++) {
          if (IsUConstant(lit.arg(j)) && IsUConstant(lit.arg(k)))
            continue;
          z.thecube->push(lit.arg(j) != lit.arg(k), ts.next(lit.arg(j) != lit.arg(k)));
        }
      }
      z.thecube->erase(i);
      continue;
    }
    i++;
  }
  if (exploded) {
    //fmt::print(cerr, "cube after explode: {}\n", z);
  //BREAK_INTO_DEBUGGER;
  }
#endif
  
  // MUS generalization on z
  auto num_mus_queries_start = stats_.num_mus_queries;
  int64_t num_mus_keep = 0, num_mus_discard = 0;
  for (size_t i = 0; z.thecube->size() > 1 && i < z.thecube->size(); ) {
    auto lit = (*z.thecube)[i];
    TimedCube t(make_shared<Cube>(*z.thecube, lit), z.frame);
    if (!solver_->IsInitial(*t.thecube)) {
      logger.Log(5, "generalizing subcube t: {}", t);
      auto num_lits_before = z.thecube->size();
      ++stats_.num_mus_queries;
      if (!CondAssign(z, solver_->SolveRelative(t))) {
        i++; // not blocked, keep literal and advance
        num_mus_keep++;
      } else {
        auto num_lits_after = z.thecube->size();
        nlogger.Log("generalize",
                    "  cube with {} literals blocked, reduced by {}",
                   num_lits_before, num_lits_before-num_lits_after);
        num_mus_discard++;
      }
      //if (traceQueryTimes && ++start % every == 0) {
      //  TRACE("    [gen eavg:{:.3f} ms]\n", T.avg);
      //}
    } else { // isInitial, so advance
      i++;
      logger.Log(5, "never mind, not generalizing subcube t [it's in I]: {}", t);
      num_mus_keep++;
    }
  }
  ret.push_back(z);
  if (z.frame == frame_inf()) {
    logger.Log(4, "program invariant: impossible to reach cube with {} literals", z.thecube->size());
    logger.Log(4, "{}", *z.thecube);
    //BREAK_INTO_DEBUGGER;
  }
  logger.Log(5, "    MUS(s): {}", *z.thecube);
  
  assert(ret.size() == 1 || ret.size() == 2);
  auto num_queries_for_cube = stats_.num_mus_queries - num_mus_queries_start;
  if (num_queries_for_cube)
    nlogger.Log("generalize",
                "summary: {} mus queries ({} literals kept, {} discarded)",
               num_queries_for_cube, num_mus_keep, num_mus_discard);
  return ret;
}


inline bool Checker::IsBlocked(const TimedCube& s) {
  // Fast syntactic check
  for (size_t d = s.frame; d < F.size(); d++) {
    for (const auto& cube : F[d]) {
      if (cube->subsumes(*s.thecube)) {
        logger.Log(5, "cube blocked due to subsumption by cube F{}: {}", d, *cube);
        ++stats_.num_subsumption_blocked;
        return true;
      }
    }
  }

  // Syntactic check didn't work, do the real check.
  auto b = solver_->IsBlocked(s);
  return b;
}


bool Checker::PropagateBlockedCubes() {
  ScopedTimeKeeper t(&stats_.forward_propagate_time);
  logger.Log(5, "[forward propagation]");
  
  for (int k = 1; k < depth(); k++) {
#ifdef DIRTYBIT
    if (!D[k]) continue;
#endif
    vector<shared_ptr<Cube>> Fk = F[k];
    for (const auto& cube : Fk) {
      ++stats_.num_propagate_queries;
      auto s = solver_->SolveRelative(TimedCube(cube, k+1), CheckerSat::NoInd);
      if (s.frame > 0) {
        logger.Log(5, "    (pushing cube from {:d} -> {:d}: {})", k, s.frame, *s.thecube);
        AddBlockedCube(s, false /*s.thecube->size() < cube->size()*/); // can change Fk
        if (cube->size() == 1 && z3::eq((*cube)[0], expr_not(xsys_.property())) &&
            s.frame == depth()) {
          if (F[k].size() == 0) {
            goto set_invariant;
          } else {
            return false;
          }
        }
      }
    }
#ifdef DIRTYBIT
    D[k] = false;
#endif
    if (F[k].size() == 0) {
    set_invariant:
      invariant_frame_ = k;
      logger.Log(5, "    invariant found (at {})", k);
      return true; // invariant found
    }
  }
  return false;
}
  
  
void Checker::AddBlockedCube(const TimedCube& s, const bool
#ifdef DIRTYBIT
                             filthy
#endif
                             ) {
  int k = min(s.frame, depth()+1);

#ifdef DIRTYBIT
  for (int d = filthy?max(1,k-1):1; d < k+1; d++) {
    if (filthy) D[d] = true;
#else
  for (int d = 1; d < k+1; d++) {
#endif
    size_t i = 0;
    auto& frame = F[d];
    while (i < frame.size()) {
      if (s.thecube->subsumes(*frame[i])) {

#ifdef CUBE_HISTORY
        s.thecube->history.push_back(d);
#endif

        frame[i] = frame[frame.size()-1];
        frame.pop_back();
      } else {
        i++;
      }
    }
  }
  F[k].push_back(s.thecube);
  ++stats_.num_added_cubes;
  solver_->BlockCubeInSolver(s);
}

void Checker::AddLemma(shared_ptr<AbstractLemmaClause> lemma) {
  staged_lemmas_.push_back(lemma);
}


void Checker::FlushStagedLemmas() {
  if (staged_lemmas_.empty()) {
    return;
  }
  if (euforia_config.check_for_redundant_lemmas) {
    // Asserts that not _all_ lemmas are redundant
    auto lemma_is_redundant = [&](auto&& l) {
      return solver_->is_lemma_redundant(l->as_expr());
    };
    // XXX should be EASSERT after the bug is found
    assert(!boost::algorithm::all_of(staged_lemmas_, lemma_is_redundant));
    _unused(lemma_is_redundant);
  }
  // Adds all lemmas to solver
  for (auto& l : staged_lemmas_) {
    solver_->AddLemmaInSolver(l);
  }
  staged_lemmas_.clear();
}

void Checker::AddBackground(z3::expr e) {
  solver_->AddBackground(e);
}



void Checker::CheckInvariant() {
  logger.Log(3, "verifying invariant");
  assert(invariant_frame_ > 0);
  solver_->Push();
  // P & Rk & T & (!Rk+ || !P+) is UNSAT
  ExprSet assumps;
  assumps.insert(!solver_->notp_act_);
  solver_->AddLemmaAssumps(assumps);
  solver_->Add(xsys_.property());
  vector<z3::expr> notRkPlus;
  for (size_t i = 0; i < F.size(); i++) {
    assumps.insert(i >= static_cast<size_t>(invariant_frame_) ? solver_->F_act_[i] : !solver_->F_act_[i]);
    if (i >= static_cast<size_t>(invariant_frame_)) {
      auto& frontier = F[i];
      for (auto& cube : frontier) {
        notRkPlus.push_back(cube->asExprNext());
      }
    }
  }
  auto notPplus = xsys_.prime(expr_not(xsys_.property()));
  solver_->Add(std::accumulate(notRkPlus.begin(), notRkPlus.end(), ctx().bool_val(false), expr_or) || notPplus);
  auto result = solver_->Check(assumps);
  if (result != CheckResult::kUnsat) {
    solver_->Print(std::cerr);
    fmt::print(cerr, "assumps:\n");
    for (auto& assump : assumps)
      fmt::print(cerr, "{} ", assump);
    fmt::print(cerr, "\n");
    auto model = solver_->get_model();
    if (is_literal_true(model->Eval(notPplus))) {
      fmt::print(cerr, "!P holds: {}\n", notPplus);
    }
    for (auto& lit : notRkPlus) {
      if (is_literal_true(model->Eval(lit))) {
        fmt::print(cerr, "!Rk lit holds: {}\n", lit);
      }
    }
    
    EUFORIA_FATAL("checkInvariant failed");
  }
  logger.Log(3, "[invariant check P & Rk & T & !(Rk+ & P+) is UNSAT]");
  solver_->Pop();
}



vector<z3::expr> Checker::InductiveInvariant() {
  assert(invariant_frame_ > 0);
  vector<z3::expr> clauses;
  for (size_t i = 0; i < F.size(); i++) {
    if (i >= static_cast<size_t>(invariant_frame_)) {
      auto& frontier = F[i];
      for (auto& c : frontier) {
        auto clause = c->negation();
        clauses.push_back(clause);
      }
    }
  }
  return clauses;
}

#if 0
void Checker::findFrameLocations() {
  unordered_map<size_t, unsigned> Floc;
  unsigned pos = 0;
  int hitCount = 0;
  int hit1Count = 0;
  unsigned firstDataFrame = 0;
  for (auto& frame : F) {
    for (auto& c : frame) {
      if (c->size() == 1) {
        auto& locExpr = (*c)[0];
        if (ts.isLocation(locExpr)) {
          size_t ID;
          bool found = ts.getIPRep().getID(locExpr, ID);
          assert(found);
          Floc.insert({ID, pos});
          
          // is this a successor of a node from previous frame
          stg_node& n = ts.stg.getNode(ID);
          for (const auto& e : n.incomingEdges) {
            auto predLoc = Floc.find(e->pred.getID());
            if (predLoc != Floc.end()) {
              auto predPos = predLoc->second;
              if (predPos < pos) {
                hitCount++;
              }
              if (predPos+1==pos)
                hit1Count++;
            }
          }
        } else if (firstDataFrame == 0) {
          firstDataFrame = pos;
        }
      } else {
        if (firstDataFrame == 0)
          firstDataFrame = pos;
      }
    }
    
    
    pos++;
  }

//    fmt::print(cerr, "hitCounts: {}, {}; fdf: {}\n", hitCount, hit1Count, firstDataFrame);
}
#endif

  



}
