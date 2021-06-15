// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef euforia__ReachabilityGraph__
#define euforia__ReachabilityGraph__

#include <boost/optional/optional.hpp>
#include <cstdint>
#include <memory>
#include <tuple>
#include <vector>

#include "cube.h"
#include "supp/expr_substitution.h"


namespace euforia {

//^----------------------------------------------------------------------------^

  
  class AbstractModel;
  class TransitionSystem;
  struct TSlice;
  class ReachabilityGraph;

//^----------------------------------------------------------------------------^
//ReachStep

//! Represents one step in reachability which means a state, plus optional info
//about stepping once from this state (if it HasTransition): a slice and model
//of the transition. The model is the one that the EUF solver found at the time
//the transition from this state was satisfied.
class ReachStep {
 public:

  inline bool HasTransition() const {
    return bool(next_state_);
  }

  //! If has_transition() is false, then there is NO state_transition() and NO
  //! model()
  inline bool has_transition() const {
    return bool(next_state_);
  }

  inline const Cube& state() const {
    return *state_.thecube;
  }

  //! Precondition: has_transition()
  inline const Cube& next_state() const {
    assert(has_transition());
    return *next_state_->thecube;
  }

  //! Precondition: has_transition()
  inline AbstractModel& step_model() const {
    assert(has_transition());
    return *step_model_;
  }
  
  // input i carries step i to i+1
  const ExprSet& input() const;

  int state_index() const { return state_index_; }
  //! \precondition @has_transition() is true
  int input_index() const {
    assert(has_transition());
    return state_index_+1;
  }
  int next_state_index() const {
    assert(has_transition());
    return state_index_+1;
  }

  inline const TSlice& state_transition() const {
    assert(has_transition());
    return *slice_;
  }

  inline bool operator==(const ReachStep& other) const {
    return state_ == other.state_ && step_model_ == other.step_model_ &&
        slice_ == other.slice_;
  }

 private:
  friend class ReachStepIterator;
  TimedCube state_;
  boost::optional<TimedCube> next_state_;
  std::shared_ptr<AbstractModel> step_model_;
  std::shared_ptr<TSlice> slice_;
  int state_index_;

  ReachStep(const TimedCube& c,
            const boost::optional<TimedCube>& n,
            const std::shared_ptr<AbstractModel>& m,
            const std::shared_ptr<TSlice>& s,
            int index) 
      : state_(c), next_state_(n), step_model_(m), slice_(s),
        state_index_(index) {}
};

std::ostream& operator<<(std::ostream&, const ReachStep&);

//^----------------------------------------------------------------------------^
//ReachStepIterator

class ReachStepIterator {
 public:
  using difference_type = int;
  using value_type = ReachStep;
  using pointer = ReachStep*;
  using reference = ReachStep&;
  using iterator_category = std::input_iterator_tag;

  inline bool operator==(const ReachStepIterator& it) const {
    return &graph_ == &it.graph_ && step_ == it.step_;
  }

  inline bool operator!=(const ReachStepIterator& it) const {
    return !(*this == it);
  }

  inline const ReachStep& operator*() { return *step_; }
  inline const ReachStep *operator->() { return &*step_; }

  ReachStepIterator& operator++();

 private:
  friend class ReachabilityGraph;

  ReachStepIterator(const ReachabilityGraph& g, TimedCube start, int index);
  ReachStepIterator(const ReachabilityGraph& g) : graph_(g), step_() {}
  
  const ReachabilityGraph& graph_;
  boost::optional<ReachStep> step_;
};

//^----------------------------------------------------------------------------^
//ReachabilityGraph
 
/// Graph that keeps track of predecessor states for doing reachability and
//constructing counterexamples
class ReachabilityGraph {
public:
  const int depth_;
  const uint64_t nrbc_;

  /// \param depth current depth of the frames
  /// \param num_backward_reach num proof obligations in reachability processed
  //so far
  ReachabilityGraph(int depth, uint64_t num_backward_reach,
                    const TransitionSystem& sts);
  ~ReachabilityGraph();
  
  /// Sets init and makes this reachability graph a Counterexample
  /// Deletes all cubes & edges not reachable from init
  void SetInit(TimedCube i);

  bool has_init() const { return bool(init_); }
  const Cube& init() const { return *init_.thecube; }
  
  // label - graph label
  void as_dot(std::ostream &str, const std::string& label) const;
  
  //! After calling SetInit(), iterates over the counterexample starting from
  //the initial state
  ReachStepIterator cx_begin() const;
  ReachStepIterator cx_end() const;
  size_t cx_length() const;
  
  //! Iterates over the counterexample in reverse. Returns begin and end
  //! iterators
  std::pair<std::vector<ReachStep>::const_reverse_iterator,
            std::vector<ReachStep>::const_reverse_iterator>
  cx_reverse_range() const;

  z3::context& ctx() const;

  z3::expr bmc_formula() const;
  ExprSubstitution mk_renamer(int64_t i) const;
  ExprSubstitution mk_input_renamer(int64_t i) const;
  ExprSubstitution mk_next_renamer(int64_t i) const;
  z3::expr get_step_var(int64_t i, const z3::expr& e) const;
  
private:
  friend class Checker;
  friend class ReachStepIterator;

  // maps Cube z -> s i, where z steps to s on model/inputs i
  std::unordered_map<std::shared_ptr<Cube>,
      std::tuple<std::shared_ptr<AbstractModel>, TimedCube, uint64_t>> 
          transition_;
  
  std::unordered_map<std::shared_ptr<Cube>, std::shared_ptr<TSlice>> easy_next_;

  // maps cube to generalized cube and step it was generalized in
  tcube_umap<std::pair<TimedCube, int>> generalized_;

  TimedCube init_; //initially empty
  // used for cx_reverse_range
  std::vector<ReachStep> cx_steps_;
  
  const TransitionSystem& sts_;
  
  /// Add that cube z reaches cube s using inputs
  /// \param n s is the n'th proof obligation
  void AddReachable(
      uint64_t n, TimedCube z, TimedCube s,
      std::shared_ptr<AbstractModel> model, std::shared_ptr<TSlice> sSliceT);

  /// Add that cube z is the unreachable (generalized) version of s
  /// \param n s is the n'th proof obligation
  void AddUnreachable(uint64_t n, TimedCube z, TimedCube s);


};

std::ostream& operator<<(std::ostream&, const ReachabilityGraph&);

}

#endif /* defined(__euforia__ReachabilityGraph__) */
