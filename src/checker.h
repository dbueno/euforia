// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef euforia__checker
#define euforia__checker

#include "checker_types.h"
#include "checkersat.h"
#include "cube.h"
#include "supp/statistics.h"
#include "xsys/transition_system.h"



namespace euforia {
class Checker;
class Counterexample;
class TransitionSystem;
class ReachabilityGraph;
  

/*-----------------------------------------------------------------------------------*/
// Checker manages frontiers and backwards reachability

class Checker {
 public:
  friend class CheckerSat;
  friend class AbstractChecker;

  struct Stats {
    /// Total number of proof obligations examined during backward reachability
    int64_t num_backward_reach = 0;
    int64_t num_cti_queries = 0; // num one step CTI checks
    int64_t num_pic_queries = 0; // num one step checks to push blocked cube to next frame
    int64_t num_mus_queries = 0; // num one step checks for generalization
    int64_t num_propagate_queries = 0; // num one step queries during prop
    int64_t num_added_cubes = 0;
    int64_t num_subsumption_blocked = 0;
    TimerDuration backward_reach_time;
    TimerDuration forward_propagate_time;
    TimerDuration generalize_time;

    Stats()
        : backward_reach_time(0), forward_propagate_time(0),
          generalize_time(0) {}

    void Reset() { (*this) = {}; }
  };

  Stats stats_;

  /// Transition system being checked
  const TransitionSystem& xsys_;
 
  explicit Checker(const TransitionSystem &xsys_);
  ~Checker(); // need this because of incomplete type unique_ptr
  Checker(const Checker&) = delete;
  Checker& operator=(const Checker&) = delete;

  /// Returns true if there is a Counterexample. Get it with
  //@computeCounterexample(). Otherwise, the property is proved. Get it with
  //dotInvariant().
  bool Run();
  
  inline z3::context& ctx() { return xsys_.ctx(); }
  
  
  inline void NewFrame();
  bool IsBlocked(const TimedCube& c);
  void AddBlockedCube(const TimedCube& s, const bool filthy = true /*if true, sets dirty bit*/);
  // Returns true if there's a Counterexample. Otherwise it doesn't.
  bool BackwardReachability(TimedCube tc);
  std::vector<TimedCube> Generalize(TimedCube blocked, TimedCube origBlocked);
  // true if invariant found, false otherwise
  bool PropagateBlockedCubes();
  
  inline bool CondAssign(TimedCube& s, TimedCube t) { 
    // if t is blocked, assign it to s and return true
    if (t.frame != kFrameNull) { s = t; return true; }
    else { return false; }
  }

  inline int depth() const { return static_cast<int>(F.size()) - 2; }
  inline int frame_inf() const { return static_cast<int>(F.size()) - 1; }
  inline const ReachabilityGraph& reachability_graph() const {
    return *reach_graph_;
  }
  std::unique_ptr<ReachabilityGraph> take_reachability_graph() {
    return std::move(reach_graph_);
  }
  
  // once solved, this can be called to make sure it's actually an invariant
  void CheckInvariant();
  // returns the clauses in the invariant
  std::vector<z3::expr> InductiveInvariant();

  //! Between invocations to Run(), lemmas may be added here
  void AddLemma(std::shared_ptr<AbstractLemmaClause> lemma);
  //! Adds a background assertion to the checker state
  void AddBackground(z3::expr);
  
  void PrintState(int log_level) const;
  void SummarizeFrames(int log_level) const;

  void PrintAssertions();
  
  void collect_statistics(Statistics *st) const;
  
 private:
  std::unique_ptr<CheckerSat> solver_;
  std::vector<std::vector<std::shared_ptr<Cube>>> F; // frames
  std::vector<std::shared_ptr<AbstractLemmaClause>> staged_lemmas_;

#ifdef DIRTYBIT
  std::vector<bool> D; // dirty bit for frames F
#endif
  // termination state: either a Counterexample
  std::unique_ptr<ReachabilityGraph> reach_graph_;
  // ...  or an invariante frame
  int invariant_frame_;
  
  // when the Checker is used by the AbstractChecker, it may be invoked
  // multiple times. this keeps track of that.
  size_t runID;

  void DumpCx(const ReachabilityGraph&) const;
  void DumpReachGraph(const ReachabilityGraph&) const;
  void FlushStagedLemmas();
  
};

}
#endif /* defined(__euforia__checker__) */
