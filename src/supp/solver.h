// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef _EUFORIA_SUPP_GENERIC_SOLVER_H_
#define _EUFORIA_SUPP_GENERIC_SOLVER_H_

#include <boost/optional/optional.hpp>
#include <iostream>
#include <memory>
#include <z3++.h>
#include <vector>

#include "supp/expr_iterators.h"
#include "supp/expr_supp.h"
#include "supp/optional_ref.h"
#include "supp/statistics.h"


namespace euforia {
//! The answer the solver returned
enum class CheckResult {
  kSat, kUnsat, kUnknown
};

std::ostream& operator<<(std::ostream&, const CheckResult& r);

//! Represents an assignment to a variable
class Assignment {
 public:
  explicit Assignment(z3::expr var, z3::expr val) : var_(var), val_(val) {}
  virtual ~Assignment() {}

  //! Returns the assignment as a constraint on var
  virtual z3::expr as_constraint(const z3::expr& var) const {
    return var == val_;
  }

 protected:
  z3::expr var_;
  z3::expr val_;
};

//! The satisfying assignment. Models must be standalone and not require the
//! corresponding Solver to be in any particular state.
class Model {
 public:
  virtual ~Model() = default;
  //! Evaluates the given expression using the model. For instance, if e is a
  //! bit vector, this method returns a (constant) bit vector of the same width
  //! as e, representing the value of e.
  //
  //! @param completion - whether the model should be completed to evaluate e
  virtual z3::expr Eval(const z3::expr& e, bool completion = false) = 0;

  //! Returns an assignment. The return value stands alone apart from the Model
  virtual std::unique_ptr<Assignment> assignment(z3::expr var);

  virtual std::ostream& Print(std::ostream&) const = 0;

  virtual void collect_statistics(Statistics *st) const = 0;
};

inline std::ostream& operator<<(std::ostream& os, const Model& m) {
  return m.Print(os);
}


//! When you subclass a solver, you need to provide a bunch of methods and keep
//! track of some statistics. Read over the class to find out that they are.
//!
//! In order to get unsat cores, you have to do the following:
//! 1. Instead of Add()'ing formulas directly, first track them with
//!    TrackAssertion and build up a list of the tracking Booleans.
//! 2. Call Check(tracking_boolean_list)
//! 3. Coll unsat_core() and then get the tracked versions from it, or
//! 4. Call unsat_core_reasons() to get the formulas directly
class Solver {
 public:
  virtual ~Solver() = default;

  // XXX add this
  // virtual std::unique_ptr<Solver> clone() = 0;

  virtual z3::context& ctx() const = 0;
  
  //! Pushes a backtracking point onto the solver context
  virtual void Push() {
    throw std::runtime_error("this Solver doesn't implement Push");
  }
  
  //! Pops the last backtracking point (from Push())
  virtual void Pop() {
    throw std::runtime_error("this Solver doesn't implement Pop");
  }
  
  //! Adds an assertion to the logical context
  virtual void Add(const z3::expr& e) = 0;

  //! Adds p => e where p is assumed to be a Boolean variable
  virtual void Add(const z3::expr& e, const z3::expr& p) {
    Add(z3::implies(p, e));
  }
 
  //! Check with assumptions
  //! I didn't default these parameters to 0 and nullptr because the default
  //! that are used are statically decided
  virtual CheckResult Check(const size_t n,
                            const z3::expr* assumptions) = 0;

  CheckResult Check() { return Check(0, nullptr); }

  CheckResult Check(const std::vector<z3::expr>& assumptions) {
    return Check(assumptions.size(), assumptions.data());
  }
  
  CheckResult Check(const ExprSet& assumptions) {
    std::vector<z3::expr> assumptions_vec(assumptions.size(), z3::expr(ctx()));
    std::copy(assumptions.begin(), assumptions.end(), assumptions_vec.begin());
    return Check(assumptions_vec);
  }

  CheckResult Check(const z3::expr_vector& assumptions) {
    std::vector<z3::expr> assumps;
    assumps.reserve(assumptions.size());
    for (int i = 0; i < static_cast<int>(assumptions.size()); i++) {
      assumps.push_back(assumptions[i]);
    }
    return Check(assumps.size(), assumps.data());
  }
  
  //! Returns the model for satisfiable problems
  virtual std::shared_ptr<Model> get_model() = 0;

  //! Gets a model with information about which vars you need.
  //!
  //! This allows one to support solvers where the model is implicit and needs
  //! to be queried, like Boolector. In this method, all vars will be queried
  //! so that the model values can be cached. The default implementation just
  //! calls get_model().
  virtual std::shared_ptr<Model> get_model(const z3::expr_vector& vars) {
    (void)vars;
    return get_model();
  }
  
  //! Returns the unsat core from the solver
  virtual z3::expr_vector unsat_core() = 0;

  //! On some solvers, returns the constraints behind the tracking Booleans
  //! that unsat_core returns.
  virtual z3::expr_vector unsat_core_reasons() = 0;

  // virtual z3::expr_vector muses() = 0;

  //! Returns the list of assertions in the logical context
  virtual z3::expr_vector assertions() const = 0;

  //! Returns the reason for the solver returning kUnknown (can be empty
  //! string)
  virtual std::string reason_unknown() const = 0;

  //! Prints the assertions and possibly other solver state
  virtual std::ostream& Print(std::ostream&) const = 0;

  //! Dump the solver state as a benchmark to the given stream
  virtual void DumpBenchmark(
      std::ostream&, size_t n, const z3::expr* assumptions) = 0;

  void DumpBenchmark(
      std::ostream& os, const std::vector<z3::expr>& assumptions) {
    return DumpBenchmark(os, assumptions.size(), assumptions.data());
  }

  virtual const char *version() const = 0;

  // Stats that subclasses should add to
  int num_solve_calls() const { return num_solve_calls_; }
  int num_solve_sat_calls() const { return num_solve_sat_calls_; }
  int num_solve_unsat_calls() const { return num_solve_unsat_calls_; }
  int num_unsat_core_calls() const { return num_unsat_core_calls_; }
  
  // tracking functions
  
  //! Associates a fresh Boolean with e and tracks it in the solver. Returns
  //! the tracking Boolean.
  virtual z3::expr TrackAssertion(const z3::expr& e, const char *prefix=nullptr);
  virtual bool IsTracked(const z3::expr&) const;
  virtual z3::expr GetTracked(const z3::expr& b) const;
  virtual z3::expr GetTracked(const z3::expr& e, const z3::expr& def) const;
  virtual void ClearTracked();

  // Writes statistics from this object into the argument. Default
  // implementation keeps track of stats on the number of calls.
  virtual void collect_statistics(Statistics *st) const {
#define upd(stat) \
    st->Update(#stat, stat ## _)
    upd(num_solve_calls);
    upd(num_solve_sat_calls);
    upd(num_solve_unsat_calls);
    upd(num_unsat_core_calls);
#undef upd
  }

 protected:
  ExprMap<z3::expr> tracked_assertions_;
  // inverse of tracked_assertions_
  ExprMap<z3::expr> tracking_bools_;

  int64_t num_solve_calls_ = 0;
  int64_t num_solve_sat_calls_ = 0;
  int64_t num_solve_unsat_calls_ = 0;
  int64_t num_unsat_core_calls_ = 0;
};
}

#endif
