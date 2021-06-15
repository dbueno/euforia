// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_REFINER_H_
#define EUFORIA_REFINER_H_

#include <boost/range/algorithm/transform.hpp>

#include "abstract_checker_impl.h"
#include "supp/expr_stats.h"
#include "supp/model_justifier.h"
#include "supp/z3_solver.h"
#include "supp/shared_container_iterator.hpp"

namespace euforia {

class Solver;

class Refiner {
 public:
  Refiner(AbstractChecker::Impl& achk,
          const std::shared_ptr<Solver>& s, int64_t nr) 
      : achk_(achk), axsys_(achk.axsys()), solver_(s), num_refinements_(nr) {}

  ExprStats& stats() { return stats_; }

  inline z3::context& ctx() const { return achk_.ctx(); }

  inline const ConcreteVmtTransitionSystem& cxsys() const {
    return achk_.cxsys();
  }
  
  inline const AbstractVmtTransitionSystem& axsys() const {
    return achk_.axsys();
  }

  void set_solver(const std::shared_ptr<Solver>& s) {
    solver_ = s;
  }

 protected:
  AbstractChecker::Impl& achk_;
  AbstractVmtTransitionSystem& axsys_;
  std::shared_ptr<Solver> solver_;
  const int64_t num_refinements_;

  Solver& solver() { return *solver_; }

  //! Returns range of abstract transition predicates that were sliced from T
  //! using the given model
  auto sliced_trans_predicates(AbstractModel& transition_model) {
    auto evaler = [&](auto&& e, bool c) {
      return transition_model.Eval(e, c);
    };
    auto predicates = std::make_shared<ExprSet>();
    ModelJustifier justify(evaler);
    logger.LogOpenFold(6, "computing predicates for T using ACX model");
    auto elt = {axsys_.trans()};
    logger.LogOpenFold(6, "computing predicates for {}", axsys_.trans());
    justify.ComputePredicates(begin(elt), end(elt), predicates.get());
    logger.LogCloseFold(6, "");
    logger.LogCloseFold(6, "");

    return make_shared_container_range<ExprSet>(predicates);
  }
  
  //! Copies *concrete* trans predicates by justifying the abstract model
  template <class OutputIt>
  void copy_trans_predicates(AbstractModel& transition_model, 
                             OutputIt assumptions_out) {
    auto concretize = [&](auto&& e) {
      return axsys_.Concretize(e);
    };
    boost::transform(sliced_trans_predicates(transition_model), assumptions_out,
                     concretize);
  }
  
  
  //! Copies *concrete* trans predicates by justifying the abstract model
  template <class OutputIt>
  void copy_input_based_trans_predicates(const ExprSet& constraints, 
                                         OutputIt assumptions_out) {
    // Make a model just from the input constraints so the justifier uses that.
    Z3Solver s(ctx(), "QF_UF");
    for (auto& c : constraints) {
      s.Add(c);
    }
    auto result = s.Check();
    assert(result == CheckResult::kSat);
    _unused(result);
    AbstractModel transition_model(s.get_model(), axsys_);
    for (auto& c : constraints) {
      transition_model.Add(c);
    }
    auto concretize = [&](auto&& e) { return axsys_.Concretize(e); };
    auto evaler = [&](auto&& e, bool c) { return transition_model.Eval(e, c); };
    ExprSet trans_predicates;
    int64_t num_trans_predicates = 0;
    ModelJustifier justify(evaler);
    logger.LogOpenFold(6, "simplifying T with input constraints");
    logger.Log(6, "T: {}", axsys_.trans());
    auto simpler_trans = justify.Simplify(axsys_.trans(), &trans_predicates);
    logger.Log(6, "simplified T: {}", simpler_trans);
    num_trans_predicates += trans_predicates.size();
    transform(trans_predicates.begin(), trans_predicates.end(),
              assumptions_out, concretize);
    boost::transform(ExprConjuncts(simpler_trans), assumptions_out,
                     concretize);
    logger.LogCloseFold(6, "");
  }

  ExprStats CalculateStats(const vector<z3::expr>& exprs) {
    ExprStats calc_stats;
    for_each(exprs.begin(), exprs.end(), calc_stats);
    return calc_stats;
  }
  
 private:
  ExprStats stats_;
};

} // end namespace euforia

#endif
