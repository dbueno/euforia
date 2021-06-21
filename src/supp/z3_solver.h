// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef tracking_solver_hpp
#define tracking_solver_hpp

#include <memory>
#include <deque>

#include "checker_types.h"
#include "supp/expr_supp.h"
#include "supp/solver.h"
#include "supp/pp/doc.h"

namespace euforia {

std::string ToSmt2WithAssumps(const z3::expr_vector& assertions,
                              const ExprSet& assumps,
                              const std::string& name,
                              const std::string& logic);

class Z3Assignment : public Assignment {
 public:
  Z3Assignment(z3::expr var, z3::expr val) : Assignment(var, val) {}

  virtual z3::expr as_constraint(const z3::expr&) const;
};

class Z3Model : public Model {
 public:
  Z3Model(const z3::model& m) : model_(m) {}
  Z3Model(z3::model&& m) : model_(std::move(m)) {}
  virtual ~Z3Model() override {}

  virtual z3::expr Eval(const z3::expr& e, bool c) override;

  virtual std::unique_ptr<Assignment> assignment(z3::expr var) override;
  
  virtual std::ostream& Print(std::ostream& os) const override {
    os << model_;
    return os;
  }

  virtual pp::DocPtr Pp() const override;

  void collect_statistics(Statistics *st) const override;

 private:
  z3::model model_;
  mutable int64_t num_bool_evals_ = 0;
  mutable int64_t num_uninterpreted_evals_ = 0;
  mutable int64_t num_unknown_evals_ = 0;
};


//^----------------------------------------------------------------------------^
//

class Z3Solver : public Solver {
 public:
  Z3Solver(z3::context& ctx);
  //! Z3 solver. Uses the given logic.
  Z3Solver(z3::context& ctx, const char *logic);
  Z3Solver(z3::solver s);
  Z3Solver(Z3Solver&&) = default;
  virtual ~Z3Solver() override = default;
  Z3Solver(const Z3Solver&) = delete;
  Z3Solver& operator=(const Z3Solver&) = delete;

  void set_params(const z3::params& p) {
    solver_.set(p);
  }
  
  virtual inline z3::context& ctx() const override { return solver_.ctx(); }

  virtual void Push() override;

  virtual void Pop() override;

  virtual void Add(const z3::expr& e) override;

  virtual CheckResult Check(const size_t n,
                            const z3::expr* assumptions) override;
  using Solver::Check;
  
  virtual z3::expr_vector unsat_core() override {
    ++num_unsat_core_calls_;
    return solver_.unsat_core();
  }
  
  virtual z3::expr_vector unsat_core_reasons() override;
  
  virtual std::string reason_unknown() const override {
    return solver_.reason_unknown();
  }
  
  virtual std::shared_ptr<Model> get_model() override;
  inline z3::model z3_model() { return solver_.get_model(); }
  virtual z3::expr_vector assertions() const override {
    return solver_.assertions();
  }

  virtual std::ostream& Print(std::ostream& os) const override {
    printAssertions(0);
    return os;
  }

  virtual void DumpBenchmark(
      std::ostream& os, size_t n, const z3::expr* assumptions) override;
  using Solver::DumpBenchmark;
  
  void printAssertions(int log_level) const;
  
  virtual const char *version() const override {
    return "Z3Solver";
  }

  virtual void collect_statistics(Statistics *) const override;
  
 protected:
  z3::solver solver_;

  z3::check_result ProcessCheck(const z3::check_result&);

  CheckResult TranslateResult(z3::check_result r) {
    switch (r) {
      case z3::check_result::sat: return CheckResult::kSat;
      case z3::check_result::unsat: return CheckResult::kUnsat;
      case z3::check_result::unknown: return CheckResult::kUnknown;
    }
    EUFORIA_FATAL("you had only three jobs...");
  }
};

}

#endif
