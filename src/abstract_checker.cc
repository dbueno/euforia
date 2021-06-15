// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "abstract_checker.h"

#include <sstream>

#include "checker.h"
#include "counterexample.h"
#include "supp/euforia_config.h"
#include "abstract_checker_impl.h"

using namespace std;
using namespace boolector;
using namespace llvm;
using namespace euforia::vmt;

//^----------------------------------------------------------------------------^

namespace euforia {

int kBtorLogLevel = 1;

//*-------------------------------------------------------------------------------*
// resolving terms via equality reasoning

#if 0
// ground terms can only contain values and state variables
static bool IsGroundTerm(const TransitionSystem& CTS, const z3::expr& e) {
  auto atom_is_ground = [&](const z3::expr& a) {
    return a.num_args() != 0 || (IsValue(a) || CTS.FindVar(a));
  };
  return all_of(po_expr_iterator::begin(e), po_expr_iterator::end(e),
                atom_is_ground);
}

template <typename OutputIt>
static void FindNonGroundAtoms(const TransitionSystem& cts,
                               const z3::expr& e, OutputIt it_out) {
  auto is_non_ground_atom = [&](const z3::expr& e) { 
    return e.num_args() == 0 && !IsGroundTerm(cts, e);
  };
  copy_if(po_expr_iterator::begin(e), po_expr_iterator::end(e), it_out,
          is_non_ground_atom);
}
#endif


//^----------------------------------------------------------------------------^
//

AbstractChecker::AbstractChecker(AbstractVmtTransitionSystem& a)
  : pimpl_(std::make_unique<AbstractChecker::Impl>(a.cts(), a, *this)),
    axsys_(a),
    cxsys_(a.cts()),
    abstraction_refinement_(true) {
  a.cts().Prepare();
}
  
// now the type ::impl is complete
AbstractChecker::~AbstractChecker() = default;


bool AbstractChecker::Run() {
  axsys_.Prepare();
  achk_ = std::make_unique<Checker>(axsys_);
  pimpl_->achk_ = achk_.get();
  while (true) {
    bool hasCx = achk_->Run();
    if (hasCx) {
      stats_.num_cx++;
      if (!abstraction_refinement_) {
        auto acx = make_unique<AbstractCounterexample>();
        acx->g_ = achk_->take_reachability_graph();
        concrete_cx_ = move(acx);
        return hasCx;
      }
      concrete_cx_ = pimpl_->RefineFromAcx(achk_->reachability_graph());
      if (concrete_cx_) {
        return true;
      }
      stats_.num_refinements++;
      // refinement may change the set of distinct constants, so assert the new
      // constraint
      achk_->AddBackground(axsys_.get_abstract_background());
    } else {        // Property holds
      return false;
    }
  }
}


std::unique_ptr<Counterexample> AbstractChecker::TakeCounterexample() {
  return move(concrete_cx_);
}


vector<z3::expr> AbstractChecker::concrete_invariant_query() const {
  // Returns I & !I'. When conjoined with T, a check-sat will verify the
  // validity of the invariant.
  vector<z3::expr> query;
  z3::expr invariant_expr(cxsys_.ctx());
  ExprAndInserter query_out(invariant_expr);
  for (const auto& clause : InductiveInvariant()) {
    *query_out++ = axsys_.Concretize(clause);
  }
  query.push_back(invariant_expr);
  query.push_back(cxsys_.prime(expr_not(invariant_expr)));
  return query;
}

void AbstractChecker::checkConcretizedInvariant() {
  assert(achk_->invariant_frame_ > 0);
  
  BoolectorSolver solver{axsys_.ctx()};
  cxsys_.AddStateUpdates(solver);
  
  vector<z3::expr> notRkplus;
  vector<z3::expr> invariant;

  vector<z3::expr> assumps;
  for (auto i = static_cast<size_t>(achk_->invariant_frame_); i < achk_->F.size(); i++) {
    auto& frontier = achk_->F[i];
    auto asserts = axsys_.ctx().bool_val(true);
    for (auto& cube : frontier) {
      // part of Rk
      auto e = axsys_.Concretize(!cube->asExpr());
      //auto n = solver.MapConcreteExpr();
      asserts = expr_and(asserts, e);
      //solver.add(n.btor_node());
      assumps.push_back(e);
      solver.Add(e);
      //solver.Assume(n, true);
      invariant.push_back(e);
      
      // part of !Rk+
      notRkplus.push_back(cube->asExprNext());
    }
    logger.Log(kLogLowest, "asserts F{}: {}", i, asserts);
  }
  
  // now Rk is in the solver
  // check that it's sat
  auto result = solver.Check(assumps);
  if (result == CheckResult::kUnsat) {
    auto failed = solver.unsat_core();
    cerr << "unsate core: " << endl;
    unsigned i = 0;
    for (const auto& fail : failed) {
      cerr << ++i << ":" << fail << endl;
    }
    //for (auto& e : invariant)
    //  cerr << e << endl;
    EUFORIA_FATAL("error: Rk is UNSAT");
  }
  
  auto notRkplusAll = std::accumulate(begin(notRkplus), end(notRkplus), axsys_.ctx().bool_val(false), expr_or);
  auto b = axsys_.Concretize(notRkplusAll);
  logger.Log(kLogLowest, "assert: {}", b);
  solver.Add(b);
  // Rk & T & !Rk+ is UNSAT
  result = solver.Check();
  if (result != CheckResult::kUnsat) {
    // XXX print assignment
    //for (auto it = cxsys_.vbegin(), ie = cxsys_.vend(); it != ie; ++it) {
    //  auto bcurr = solver.rewriteAsBtor(it->current());
    //  auto bnext = solver.rewriteAsBtor(it->next());
    //  auto bcurrAss = solver.btor_solver()->assignment(bcurr);
    //  auto bnextAss = solver.btor_solver()->assignment(bnext);
    //  cerr << *bcurrAss << " => " << *bnextAss << endl;
    //}
    EUFORIA_FATAL("[invariant check Rk & T & !Rk+ is SAT]");
  }
  logger.Log(1, "[invariant check Rk & T & !Rk+ is UNSAT]");
  for (auto& e : invariant)
    logger.Log(2, "{}", e);
}


std::vector<z3::expr> AbstractChecker::InductiveInvariant() const {
  auto clauses = achk_->InductiveInvariant();
  return clauses;
}

std::vector<z3::expr> AbstractChecker::MinimizeConcretizedInvariant() const {
  fmt::print("minimizing concrete invariant\n");
  BoolectorSolver solver{axsys_.ctx()}; // incremental
  cxsys_.AddStateUpdates(solver);
  solver.Add(cxsys_.property());

  vector<z3::expr> invariant_clauses;
  // positives[i] tracks the clause at invariant_clauses[i]
  // negativez[i] tracks the !clause' at invariant_clauses[i]
  vector<z3::expr> positives, negatives;
  for (const auto& clause : InductiveInvariant()) {
    auto c_clause = axsys_.Concretize(clause);
    invariant_clauses.push_back(c_clause);
    positives.push_back(solver.TrackAssertion(c_clause));
    negatives.push_back(solver.TrackAssertion(!cxsys_.prime(c_clause)));
  }
  // We're going to drop one clause at a time from the invariant (on
  // both sides) and test to see if it's still an invariant.  If it is,
  // the SMT problem will be unsat and we can discard the clause.  If
  // it is not, the SMT problem will be sat and we have to keep the
  // clause.  Discarding a clause will create new opportunities to drop
  // more clauses, so we do this until a pass over invariant_clauses doesn't
  // change it.
  int num_clauses_removed = 0, last_num_clauses_removed;
  do {
    last_num_clauses_removed = num_clauses_removed;
    assert(invariant_clauses.size() == positives.size());
    assert(positives.size() == negatives.size());

    // construct invariant
    ExprSet assumps;
    for (size_t i = 0; i < invariant_clauses.size();) {
      //solver.ClearAssumptions();
      z3::expr bad = !cxsys_.prime(cxsys_.property());
      int invariant_size = 0;

      // add every clause to invariant except i
      for (size_t j = 0; j < invariant_clauses.size(); j++) {
        if (j == i) {
          assumps.insert(axsys_.Concretize(!positives[j]));
          assumps.insert(axsys_.Concretize(!negatives[j]));
          continue;
        }
        assumps.insert(axsys_.Concretize(positives[j]));
        bad = bad || negatives[j];
        ++invariant_size;
      }

      assumps.insert(axsys_.Concretize(bad));
      auto result = solver.Check(assumps);
      if (result == CheckResult::kUnsat) {
        num_clauses_removed++;
        // don't need clause i, so remove it from invariant_clauses
        solver.Add(!positives[i]);
        solver.Add(!negatives[i]);
        swap(invariant_clauses[i], invariant_clauses[invariant_clauses.size()-1]);
        invariant_clauses.pop_back();
        // keep tracking literals in sync
        swap(positives[i], positives[positives.size()-1]);
        positives.pop_back();
        swap(negatives[i], negatives[negatives.size()-1]);
        negatives.pop_back();
        fmt::print(cerr, "{} ", invariant_clauses.size());
        std::flush(cerr);
      } else {
        // do need clause i
        i++;
      }
    }
  } while (last_num_clauses_removed != num_clauses_removed);

  fmt::print(cerr, "\n");
  fmt::print(cerr, "removed {} clauses from invariant\n", num_clauses_removed);

  // for property
  invariant_clauses.push_back(cxsys_.property());

  int i = 0;
  fmt::print(cerr, "minimized invariant:\n");
  for (auto& clause : invariant_clauses) {
    fmt::print(cerr, "{}: {}\n", ++i, clause);
  }

  return invariant_clauses;
}



void AbstractChecker::collect_statistics(Statistics *st) const {
  pimpl_->collect_statistics(st);
  st->Update("num_counterexamples", stats_.num_cx);
  st->Update("refinements", stats_.num_refinements);
  achk_->collect_statistics(st);
}


} // end namespace euforia

