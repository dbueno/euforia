// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_YICES_SOLVER_H_
#define EUFORIA_SUPP_YICES_SOLVER_H_

extern "C" {
#include <yices.h>
}

#include <memory>
#include <propagate_const.h>

#include "supp/solver.h"

#include <unordered_map>

namespace euforia {
namespace yices_supp {

class Solver;
class Z3YicesExprPair;
class YicesToZ3Rewriter;
class Z3ToYicesRewriter;

class Model : public euforia::Model {
 public:
  Model(Solver& s);
  ~Model();
  //! Evaluates the given expression using the model. For instance, if e is a
  //! bit vector, this method returns a (constant) bit vector of the same width
  //! as e, representing the value of e.
  //
  //! @param completion - whether the model should be completed to evaluate e
  virtual z3::expr Eval(const z3::expr& e, bool completion = false) const;
  virtual std::ostream& Print(std::ostream&) const;

 private:
  Solver& solver_;
  std::shared_ptr<model_t> m_;
  class Impl;
  std::unique_ptr<Impl> pimpl_;
};


class Solver : public euforia::Solver {
  friend class Model;
 public:
  std::unordered_map<term_t, z3::expr> yices_to_z3_;

  Solver(z3::context&, const char *logic, bool tseitin = false);
  ~Solver();
  
  //! Pushes a backtracking point onto the solver context
  virtual void Push() override;
  
  //! Pops the last backtracking point (from Push())
  virtual void Pop() override;
  
  //! Adds an assertion to the logical context
  virtual void Add(const z3::expr& e) override;
  void Add(const z3::expr& e, bool) {
    return Add(e);
  }
 
  //! Checks the assertion for satisfiability
  virtual CheckResult Check() override;

  //! Check with assumptions
  virtual CheckResult Check(const ExprSet& assumptions) override;
  virtual CheckResult Check(const std::vector<z3::expr>& assumptions) override;
  
  //! Returns the model for satisfiable problems
  virtual std::shared_ptr<euforia::Model> get_model() override;
  
  //! Returns the unsat_core as a list of tracking bools for unsatisfiable
  //! problems
  virtual z3::expr_vector unsat_core() override;

  //! Returns the unsat core as the list tracked expressions for unsat problems
  virtual z3::expr_vector unsat_core_reasons() override;

  //! Returns the list of assertions in the logical context
  virtual z3::expr_vector assertions() const override { return assertions_; }

  //! Returns the reason for the solver returning kUnknown (can be empty
  //! string)
  virtual std::string reason_unknown() const override { return "shrug"; }

  //! Prints the assertions and possibly other solver state
  virtual std::ostream& Print(std::ostream&) const override;

  Z3YicesExprPair MapConcreteExpr(const z3::expr& e);

  inline z3::context& ctx() { return z3_ctx_; }

  YicesToZ3Rewriter& yices_to_z3();
  Z3ToYicesRewriter& z3_to_yices();

 private:
  class Impl;
  std::unique_ptr<Impl> pimpl_;
  z3::context& z3_ctx_;
  z3::expr_vector assertions_;

  CheckResult TranslateResult(smt_status_t r);
};

struct TermWrapper;
} // end namespace yices_supp
} // end namespace euforia

#endif
