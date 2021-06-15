// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef _EUFORIA_SUPP_PORTFOLIO_SOLVER_H_
#define _EUFORIA_SUPP_PORTFOLIO_SOLVER_H_

#include <memory>
#include <propagate_const.h>
#include <unordered_map>
#include <vector>

#include "supp/solver.h"

namespace euforia {
class Statistics;

class PortfolioSolver : public Solver {
 public:
  struct Stats {
  };

  PortfolioSolver(z3::context& ctx,
                  std::vector<std::shared_ptr<Solver>> solvers);
  ~PortfolioSolver();
  
  virtual z3::context& ctx() const { return ctx_; }

  virtual void Push();
  virtual void Pop();
  virtual void Add(const z3::expr& e);
  virtual CheckResult Check(const size_t n, const z3::expr* assumptions);
  virtual std::shared_ptr<Model> get_model();
  virtual z3::expr_vector unsat_core();
  virtual z3::expr_vector unsat_core_reasons();
  virtual z3::expr_vector assertions() const;
  virtual std::string reason_unknown() const;
  virtual std::ostream& Print(std::ostream&) const;
  virtual void DumpBenchmark(
      std::ostream&, size_t n, const z3::expr* assumptions);
  virtual const char *version() const;


  void collect_statistics(Statistics *st) const;

  class Impl;

 private:
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;
  z3::context& ctx_;

};

}

#endif

