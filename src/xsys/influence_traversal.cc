// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "xsys/influence_traversal.h"

#include <llvm/ADT/EquivalenceClasses.h>

#include "supp/equality_literal.h"
#include "supp/model_justifier.h"
#include "xsys/transition_system.h"
#include "supp/z3_solver.h"

using namespace std;
using namespace llvm;
using namespace euforia;



static void PrintHashedExpr(const z3::expr& e, string name,
                            int loglevel = 6) {
  logger.LogOpenFold(loglevel, "{} {:08x} as hashes:", name, e.hash());
  for (auto it = po_expr_iterator::begin(e),
       ie = po_expr_iterator::end(e); it != ie; ++it) {
    stringstream ss_args;
    bool first = true;
    for (const auto& arg : ExprArgs(*it)) {
      if (!first) {
        fmt::print(ss_args, " ");
      }
      fmt::print(ss_args, "{:08x}", arg.hash());
      first = false;
    }
    logger.Log(loglevel, "    {:08x}: [{:2} args] {}: {}", (*it).hash(),
               (*it).num_args(), (*it).decl().name(), ss_args.str());
  }
  logger.LogCloseFold(loglevel, "");
}


class FilterPredicates {
 public:
  FilterPredicates(const TransitionSystem& xsys,
                   const ExprSet& roots, const ExprSet& assumps) 
  : xsys_(xsys), roots_(roots), assumps_(assumps.begin(), assumps.end()) {}

  void filter(ExprSet *assumps_out) {
    // I want to separate the assumptions into two group.s The first group will
    // go into equations, which maps a variable to the set of things it was
    // found equal to.  The second is the rest of the assumptions. 
    EquivalenceClasses<z3::ExprWrapper> classes; // equation sets
    vector<z3::ExprWrapper> assumps(assumps_.begin(), assumps_.end());
    int64_t orig_assumps_size = static_cast<int64_t>(assumps.size());
    for (size_t i = 0; i < assumps.size(); /* body */) {
      const z3::expr& a = assumps[i];
      // Handle equalities and Boolean vars as equalities
      if (EqualityLiteral::is_equality(a)) {
        EqualityLiteral eq_lit(a);
        classes.unionSets(eq_lit.lhs(), eq_lit.rhs());
        // Remove expr from assumps
        swap(assumps[i], assumps[assumps.size()-1]);
        assumps.pop_back();
      } else {
        i++;
      }
    }
    // At this point, the assumps only contains those assumptions which aren't
    // equations but which were found during model justification (with
    // pruning). Here we expand the set of roots_ to include next-state and
    // input variables from these assumps. Any definitions of these roots_ in
    // our predicates are explored next. 
    logger.Log(5, "after grouping equations, here are the assumptions:");
    for (auto& a : assumps) {
      logger.Log(5, "    {}", a);
      //for (auto& e : ExprDescendents(a)) {
      //  if (ts_.HasNextStateVar(e) || ts_.FindInput(e)) {
      //    roots_.insert(e);
      //  }
      //}
    }
    logger.Log(5, "... and here are the equations:");
    int i = 0;
    for (auto cit = classes.begin(), cie = classes.end(); cit != cie; ++cit) {
      if (!cit->isLeader()) continue;
      logger.Log(5, "    class {}", ++i);
      for (auto it = classes.member_begin(cit); it != classes.member_end();
           ++it) {
        logger.Log(5, "        {}", *it);
      }
    }
    // Now, we have a worklist algorithm over relevant variables. For an unseen
    // variable, we find the equations (if any) set to that variable. These
    // equations are relevant, now, since we started at a relevant root. The
    // code (1) adds the now-relevant equality to assumps and (2) adds the
    // now-relevant rhs variables (next-state and inputs) to the worklist.
    // Finally, it marks the variable seen.
    ExprSet vars_seen;
    logger.Log(5, "roots of variables to use: {}", roots_);
    while (!roots_.empty()) {
      const z3::expr& var = *roots_.begin();
      roots_.erase(var);
      auto not_seen = vars_seen.insert(var).second;
      if (not_seen) {
        if (classes.findLeader(var) == classes.member_end()) {
          logger.Log(5, "{} not found in equation classes", var);
        }
        // Look for refs to var in equality predicates
        for (auto it = classes.findLeader(var); it != classes.member_end();
             ++it) {
          const z3::expr& rhs = *it;
          if (z3::eq(rhs, var)) {
            continue;
          }
          assumps.push_back(expr_eq(var, rhs));
          copy_if(po_expr_iterator::begin(rhs), po_expr_iterator::end(rhs),
                  inserter(roots_, roots_.end()),
                  [&](auto&& e) { return xsys_.FindVar(e) ||
                  xsys_.FindInput(e); });
        }
      }
    }
    logger.Log(5, "final visited vars: {}", vars_seen);
    logger.Log(5, "final set of assumps:");
    for (auto& a : assumps) {
      logger.Log(5, "    {}", a);
    }
    logger.Log(5, "influence excluded {} predicates out of {}",
               (orig_assumps_size - assumps.size()), orig_assumps_size);
    *assumps_out = ExprSet(assumps.begin(), assumps.end());
  }

 private:
  const TransitionSystem& xsys_;
  ExprSet roots_;
  EquivalenceClasses<z3::ExprWrapper> classes_;
  vector<z3::ExprWrapper> assumps_;
};

//^----------------------------------------------------------------------------^


class SatFilter {
 public:
  SatFilter(const TransitionSystem& xsys) 
      : xsys_(xsys), solver_(xsys.ctx(), "QF_AUFBV") {}

  void filter(ExprSet *assumps_out, const ExprSet& target) {
    vector<z3::ExprWrapper> assumps(assumps_out->begin(), assumps_out->end());
    vector<z3::expr> bools;
    bools.reserve(assumps_out->size()+1);
    for (auto& a : assumps) {
      bools.push_back(solver_.TrackAssertion(a));
      logger.Log(5, "tracking {} -> {}", bools.back(), a);
    }
    logger.Log(5, "testing {} assumps", bools.size());

    xsys_.AddTransitionsToChecker(solver_);
    for_each(target.begin(), target.end(), [&](auto&& t) { solver_.Add(t); });

    // In some order, add all assumptions to solver with a push() in between.
    // Obviously it should be sat. Pop one. Push its negation. If sat, pop and
    // that's the end of the loop. If it's unsat, keep it
    for (int i = 0; i < static_cast<int>(bools.size()); ) {
      for_each(bools.begin(), bools.end(),
               [&](auto&& e) { fmt::print("{} ", e); });
      fmt::print("\n");
      // Pick a literal to negate
      auto b = bools[i];
      // Disable the literal
      bools[i] = expr_not(b);
      // Assume its negation
      bools.push_back(solver_.TrackAssertion(expr_not(assumps[i])));
      for_each(bools.begin(), bools.end(),
               [&](auto&& e) { fmt::print("{} ", e); });
      fmt::print("\n");
      auto result = solver_.Check(bools);
      // Pop negation
      bools.pop_back();
      if (CheckResult::kSat == result) {
        logger.Log(5, "{} sat\n", expr_not(assumps[i]));
        // Sat, so get rid of literal
        swap(bools[i], bools[bools.size()-1]);
        bools.pop_back();
        swap(assumps[i], assumps[assumps.size()-1]);
        assumps.pop_back();
        // Don't change i because it's changed, look at it next
      } else {
        // Restore tracking literal
        bools[i] = b;
        i++;
      }
    }

    assumps_out->clear();
    for (auto& b : bools) {
      assumps_out->insert(solver_.GetTracked(b, b));
    }
  }

 private:
  const TransitionSystem& xsys_;
  Z3Solver solver_;
};

//^----------------------------------------------------------------------------^

class UpdateVarTraversal {
 public:
  UpdateVarTraversal(const TransitionSystem& ts) : ts_(ts) {}

  // For each predicate in assumps, traverses it and adds to the defd, used,
  // input, and constants in the influence.
  void operator()(const ExprSet& assumps, InfluenceTraversal *influence,
                  ExprSet *roots) {
    for (auto& a : assumps) {
      // We use our own visited set, visited_, to avoid traversing assumptions
      // multiple times. The assumps could contain expressions we've already
      // seen.
      for (auto it = po_expr_ext_iterator::begin(a, visited_),
           ie = po_expr_ext_iterator::end(a, visited_); it != ie; ++it) {
        const auto& e = *it;
        // Tell the influence that we encountered these leaves
        if (e.num_args() == 0) {
          if (auto var = ts_.FindVar(e)) {
            if (z3::eq(var->next(), e)) {
              influence->AddDefdVar(e);
              roots->insert(e);
            } else {
              influence->AddUsedVar(e);
            }
          } else if (ts_.FindInput(e)) {
            influence->AddUsedInput(e);
            roots->insert(e);
          } else if (IsUConstant(e)) {
            influence->AddUsedConstant(e);
          }
        }
      }
    }
  }

 private:
  const TransitionSystem& ts_;
  ExprSet visited_;
};


namespace euforia {
struct InfluenceTraversal::Impl {
  UpdateVarTraversal update_vars;
  ModelJustifier justify;
  ExprSet roots;
  ExprSet predicates;
  Impl(const TransitionSystem& xsys,
       std::function<z3::expr(const z3::expr&, bool complete)> eval) 
      : update_vars(xsys), justify(eval) {}
};

//^----------------------------------------------------------------------------^
//InfluenceTraversal
  
InfluenceTraversal::InfluenceTraversal(
    const TransitionSystem& ts, Z3EvalFunc eval,
    ExprSet *as)
    : eval_(eval), assumps_(as), ts_(ts),
    pimpl_(std::make_unique<Impl>(ts, eval))
{
}

InfluenceTraversal::~InfluenceTraversal() = default;
    

// This method is given a target set of terms. Here are the known contexts in
// which in is called:
// 1. terms = (R_k & !P) [current-state variables]
// 2. terms = a target cube. [next-state variables]
// 3. terms = a literal/formula from a lemma [current & next-state]
//
// If the terms are on current state, this code just extracts satisfied
// predicates from the terms.  If terms has any next-state variables, it
// extracts predicates from T as well.  Currently, it extracts predicates by
// pruning T using the model and justifying the model of T.
void InfluenceTraversal::operator()(const ExprSet& terms) {
  auto& roots = pimpl_->roots;
  auto& predicates = pimpl_->predicates;
  roots.clear();
  pimpl_->justify.set_num_visits(0);

  // Pick up relevant info from terms
  pimpl_->justify.ComputePredicates(terms.begin(), terms.end(), assumps_);
  // Record any variables we encountered during traversal
  pimpl_->update_vars(*assumps_, this, &roots);
  logger.Log(5, "roots of influence: {}", roots);

  if (!roots.empty()) {
    // Extract predicates from T.
    
    // The AbstractVmtTransitionSystem provides two views of the transition
    // relation. One is as a single expression and the other is a pair of (T0,
    // E), where T is T0 && E and E is a set of equations. In the code, T0 is
    // ts_.trans_rest() and E is ts_.trans_equations(). This code supports both
    // representations; it supports the latter representation in two parts.
    // Here, it iterates over the relation T0 as if it were T. If E is empty,
    // then this is all we need to do. Later in this method, it will process
    // the equations (if any).
    auto trans = {ts_.trans_rest()};
    pimpl_->justify.ComputePredicates(begin(trans), end(trans), assumps_);
    pimpl_->update_vars(*assumps_, this, &roots);

    // We now have to process E (ts_.trans_equations()), the equations of the
    // transition relation.  roots now contains all the next-state vars and
    // inputs that we've seen.  Next, iterates over a worklist of
    // root-variables (rootlist), processing them by seeing if there is an
    // equation for that variable; if so, then that equation is processed like
    // any constraint, possibly updating the rootlist and set of vars
    // encountered.
    //
    // The benefit is that some equations may be ignored -- the next-state or
    // input variables they define were never encountered so there's no need to
    // look at them.
    if (auto eq_map = ts_.trans_equations()) {
      auto eqs = eq_map->get();
      ExprSet rootlist(roots), root_seen;
      while (!rootlist.empty()) {
        auto root = *rootlist.begin();
        auto not_seen = root_seen.insert(root).second;
        rootlist.erase(root);
        if (!not_seen)
          continue;
        logger.Log(6, "searching for root equation {}", root);
        for (auto [it, ie] = eqs.equal_range(root); it != ie; ++it) {
          logger.Log(6, "searching for root equation {}: found!", root);
          const z3::expr& var = it->first;
          auto& rhs = it->second;
          auto eq_term = {var == rhs};
          predicates.clear();
          pimpl_->justify.ComputePredicates(begin(eq_term), end(eq_term),
                                            &predicates);
          pimpl_->update_vars(predicates, this, &rootlist);
          assumps_->insert(predicates.begin(), predicates.end());
        }
      }
    }
  }
  logger.Log(6, "influence visits: {}", pimpl_->justify.num_visits());
  
}
} // end namespace euforia

  



