// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef counterexample_hpp
#define counterexample_hpp

#include <memory>

#include "refinement/symex.h"
#include "supp/boolector_supp.h"
#include "supp/reachability_graph.h"


namespace symex {
class State;
}

namespace euforia {
struct TSlice;

class Counterexample {
  friend class Checker;
  friend class AbstractChecker;
  
 public:
  virtual ~Counterexample() = default;
  virtual void print(std::ostream&) const = 0;
  virtual size_t length() const = 0;
  
  
};

/*-----------------------------------------------------------------------*/

using cx_var_assignment = std::unordered_map<std::string, std::shared_ptr<boolector::BtorAssignment>>;

struct BoolectorCounterexample : public Counterexample {
  std::shared_ptr<boolector::BtorWrapper> B;
  // state # -> vector(name, value)
  std::vector<cx_var_assignment> cstates;
  std::vector<cx_var_assignment> cinputs;

  BoolectorCounterexample(std::shared_ptr<boolector::BtorWrapper> B);

  virtual size_t length() const override;
  void print(std::ostream&) const override;

};

//^----------------------------------------------------------------------------^

class SCounterexample : public Counterexample {
  friend class AbstractChecker;
 public:
  virtual ~SCounterexample() = default;

  virtual size_t length() const override {
    if (!states_.empty()) {
      return states_.size()-1;
    }
    EUFORIA_FATAL("no states in counterexample");
  }
  
  virtual void print(std::ostream& os) const override;

 private:
  std::vector<std::shared_ptr<symex::State>> states_;
};

//^----------------------------------------------------------------------------^

class BmcOneShotCounterexample : public Counterexample {
  friend class BmcOneShotRefiner;
 public:
  virtual ~BmcOneShotCounterexample() = default;

  virtual size_t length() const override { return length_; }

  virtual void print(std::ostream& os) const override {
    cx_model_->Print(os);
  }

  void set_model(const std::shared_ptr<Model>& model) {
    cx_model_ = model;
  }

 private:
  std::shared_ptr<Model> cx_model_;
  int64_t length_;
};

//^----------------------------------------------------------------------------^

class AbstractCounterexample : public Counterexample {
  friend class AbstractChecker;
 public:
  virtual ~AbstractCounterexample() = default;

  virtual size_t length() const { return g_->cx_length(); }

  virtual void print(std::ostream& out) const { out << *g_; }

 private:
  std::shared_ptr<ReachabilityGraph> g_;
};

}

#endif /* counterexample_hpp */
