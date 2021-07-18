// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include <boost/container_hash/hash.hpp>

#include "cube.h"
#include "refinement/symex.h"
#include "supp/boolector_solver.h"
#include "supp/debug.h"
#include "tslice.h"
#include "xsys/abstract_vmt_transition_system.h"

using namespace std;
using namespace llvm;

namespace euforia {
struct TSlice;
using namespace symex;
using namespace vmt;

//^----------------------------------------------------------------------------^


z3::expr BoolectorModel::Eval(const z3::expr& e, bool) {
  if (auto search = queried_.find(e); search != queried_.end()) {
    return search->second;
  }
  auto e_concrete = solver_.MapConcreteExpr(e);
  auto e_val = solver_.btor_solver()->assignment(
      e_concrete.btor_node())->AsExpr(e_concrete.z3_node());
  queried_.insert({e, e_val});
  return e_val;
}

std::ostream& BoolectorModel::Print(std::ostream& os) const {
  fmt::print(os, "BoolectorModel:\n");
  for (const auto& entry : queried_) {
    (void)entry;
    fmt::print(os, "  {}: {}\n", entry.first, entry.second);
  }
  fmt::print(os, "end BoolectorModel\n");
  return os;
}

void BoolectorModel::collect_statistics(Statistics *st) const {
  st->Update("BoolectorModel num queried",
             static_cast<int64_t>(queried_.size()));
}

/*--------------------------------------------------------------------------*/

BoolectorSolver::BoolectorSolver(z3::context& c) :
    ctx_(c), solver_(std::make_shared<BtorWrapper>()),
    z3_to_btor_(Z3ToBtorRewriter(solver_)) {
  solver_stack_.push_back(solver_);
  // solver_->setOption(BTOR_OPT_MODEL_GEN, 2);
  // solver_->setOption(BTOR_OPT_INCREMENTAL, 1);
  //getSolver()->setOption(BTOR_OPT_REWRITE_LEVEL, 0);
  //getSolver()->setOption(BTOR_OPT_VAR_SUBST, 0);
//#ifndef NDEBUG
//    getSolver()->setOption(BTOR_OPT_CHK_FAILED_ASSUMPTIONS, 0); // some wonkiness
//#endif
  // Build boolector in debug mode. Then you can set the log level and get
  // messages.
  // solver_->setOption(BTOR_OPT_LOGLEVEL, 2);
  
  //CTS_.addOneHots(*this);
  //CTS_.addStateUpdates(*this);
  //CTS_.addPreservations(*this);
  adds_to_perm_assumps_ = true;
//    CTS_.addPreservations(*this);
//    CTS_.addControlTransitions(*this);
  // put all updates in the permanent assumptions
  adds_to_perm_assumps_ = false;
  
}

BoolectorSolver::BoolectorSolver(const BoolectorSolver& other) 
  : ctx_(other.ctx_), solver_(std::make_shared<BtorWrapper>(*other.solver_)),
    z3_to_btor_(solver_) {
  // You may not copy the z3->btor rewriter instance directly because it points
  // to Btor exprs that are only valid in the source instance. This copies the
  // matched node entries explicitly
  for (const auto& entry : other.z3_to_btor_.cache()) {
    z3_to_btor_.cache().insert({entry.first,
                               btor_solver()->matchNode(entry.second)});
  }
}

std::unique_ptr<BoolectorSolver> BoolectorSolver::clone() const {
  return make_unique<BoolectorSolver>(*this);
}
 
std::shared_ptr<Model> BoolectorSolver::get_model() {
  return make_shared<BoolectorModel>(*this);
}

std::shared_ptr<Model> BoolectorSolver::get_model(const z3::expr_vector& vars) {
  auto model = get_model();
  for (const auto& v : vars) {
    model->Eval(v);
  }
  return model;
}
  
//BoolectorSolver::BoolectorSolver(const BoolectorSolver& other) :
//    solver_(make_shared<BtorWrapper>(*other.solver_)), // clone
//    ATS(other.ATS),
//    CTS_(other.CTS_),
//    rw(std::make_unique<BtorConcretizingRewriter>(*other.rw)),
//    permAssumps(other.permAssumps),
//    addsToPermAssumps(other.addsToPermAssumps),
//    assumptions(other.assumptions),
//    failTrackers(other.failTrackers)
//{}


std::size_t Z3BtorExprPair::hash() const {
  std::size_t h = z3_node();
  boost::hash_combine(h, btor_node());
  return h;
}

std::size_t hash_value(const Z3BtorExprPair& p) {
  return p.hash();
}

Z3BtorExprPair BoolectorSolver::MapConcreteExpr(const z3::expr& e) {
  return Z3BtorExprPair(e, z3_to_btor_.Rewrite(e));
}

void BoolectorSolver::Add(const z3::expr& z3Conc) {
  auto n = rewriteAsBtor(z3Conc);
  if (adds_to_perm_assumps_) {
    auto p = Z3BtorExprPair(z3Conc, n);
    permanent_assumps_.push_back(p);
  } else {
    solver_->add(n);
  }
}

void BoolectorSolver::AddGeneral(const z3::expr& z3_conc, bool is_permanent) {
  adds_to_perm_assumps_ = is_permanent;
  Add(z3_conc);
  adds_to_perm_assumps_ = false;
}

//void BoolectorSolver::Add(const BoolectorNodeWrapper& n) {
//  solver_->add(n);
//}

BoolectorNodeWrapper BoolectorSolver::Assume(
    const Z3BtorExprPair& n, bool track, const boost::optional<string>& tag) {
  assert(n.btor_node().width() == 1);
  shared_ptr<string> the_tag;
  if (tag) {
    the_tag = make_shared<string>(*tag);
  }
  assumptions_.emplace(n, move(the_tag));
  if (track)
    fail_trackers_.push_back(n);
  return n.btor_node();
}

void BoolectorSolver::Unassume(const Z3BtorExprPair& n) {
  // TODO could be more efficient if another representation
  size_t i = 0; // index of deleted element from assumptions
  for (auto it = begin(assumptions_); it != end(assumptions_);) {
    auto& [expr, label] = *it;
    (void)label;
    if (expr == n) {
      it = assumptions_.erase(it);
      break;
    } else {
      ++it;
    }
    i++;
  }
  auto it = begin(fail_trackers_);
  advance(it, i);
  fail_trackers_.erase(it);
}

void BoolectorSolver::ClearAssumptions() {
  fail_trackers_.clear();
  assumptions_.clear();
  btor_solver()->resetAssumptions();
}


BtorWrapper::result BoolectorSolver::BtorCheck(bool printAssertions) {
  logger.Log(3, "BoolectorSolver::BtorCheck ({} assumps {} failTrackers)...", 
             assumptions_.size(), fail_trackers_.size());
  for (auto& n : permanent_assumps_) {
    btor_solver()->assume(n.btor_node());
  }
  for (auto& [n, label] : assumptions_) {
    (void)label;
    btor_solver()->assume(n.btor_node());
  }
  if (printAssertions && logger.ShouldLog(4)) {
    BtorWrapper clone(*btor_solver());
    clone.fixateAssumptions();
    clone.printAssertions();
  }
  return btor_solver()->check();
}

CheckResult BoolectorSolver::Check(const size_t n,
                                   const z3::expr* assumptions) {
  ClearAssumptions();
  std::for_each(assumptions, assumptions + n,
                [this](const z3::expr& e){ Assume(MapConcreteExpr(e), true); });
  return TranslateResult(BtorCheck(false));
}

void BoolectorSolver::Push() {
  BtorWrapper clone(*solver_);
  solver_stack_.push_back(std::make_shared<BtorWrapper>(clone));
  solver_ = solver_stack_.back();
}

void BoolectorSolver::Pop() {
  solver_stack_.pop_back();
  solver_ = solver_stack_.back();
}

std::vector<std::vector<Z3BtorExprPair>>
BoolectorSolver::failed_literals() {
  // failed literal maybe be false itself or may be part of a group
  std::vector<std::vector<Z3BtorExprPair>> ret;
  int failedGroup = -1; // might be only false nodes, so handle that
  // TODO precompute list or iterate twice
  vector<Z3BtorExprPair> all_trackers{fail_trackers_};
  all_trackers.insert(all_trackers.end(), permanent_assumps_.begin(),
                      permanent_assumps_.end());
  for (auto& mbn : all_trackers) {
    auto c = mbn.z3_node();
    if (btor_solver()->isFailed(mbn.btor_node())) {
      // if the node is false all by itself put it in its own MUS
      if (boolector::eq(mbn.btor_node(), btor_solver()->boolVal(false))) {
        ret.push_back(std::vector<Z3BtorExprPair>());
        ret[ret.size()-1].push_back(mbn);
      } else {
        // otherwise put in the failed group of not-false nodes
        if (failedGroup == -1) {
          ret.push_back(std::vector<Z3BtorExprPair>());
          failedGroup = static_cast<int>(ret.size()-1);
        }
        assert(failedGroup > -1);
        ret[failedGroup].push_back(mbn);
      }
    }
  }
#ifndef NDEBUG
  for (auto& elt : ret) { assert(!elt.empty()); }
#endif
  return ret;
}



string
BoolectorSolver::GetAssumptionLabel(const Z3BtorExprPair& n) const {
  if (const auto& search = assumptions_.find(n); search != assumptions_.end()) {
    if (search->second)
      return *search->second;
  }
  return "";
}

std::vector<ExprSet>
BoolectorSolver::FindMuses(const bool multiple) {
  // this code does not do an MUS calculation
  std::vector<ExprSet> ret;
  BoolectorNodeSet failed;
  auto result = BtorWrapper::result::kUnsat;
  
  do {
    auto MUSes = failed_literals();
    logger.Log(3, "FindMuses: boolector returned {} MUS", MUSes.size());
    
    if (MUSes.empty()) {
      // can happen if we're not tracking whatever is in the core
      // hmm...
      EUFORIA_FATAL("didn't track what was unsat");
    }
    
    for (auto& MUS : MUSes) {
      assert(!MUS.empty());
      ret.push_back(ExprSet());
      stringstream ss;
      for (auto& lit : MUS) {
        ss << endl << "    " << lit.z3_node() << " [label: " <<
            GetAssumptionLabel(lit) << "]";
        // CANNOT simplify because it may simplify to false which would be tragic
        ret.back().insert(lit.z3_node());
      }
      logger.Log(3, "concrete MUS has {} literals:{}", MUS.size(), ss.str());
      // TODO some heuristic for what's best to drop?
      Unassume(*MUS.begin());
    }
    
    if (multiple)
      result = BtorCheck();
  } while (multiple && result == BtorWrapper::result::kUnsat);
  assert(!multiple || result == BtorWrapper::result::kSat);
  
  ClearAssumptions();
  
  std::sort(ret.begin(), ret.end(), [](const ExprSet& l, const ExprSet& r) -> bool { return l.size() < r.size(); });
  
//    while (ret.size() > 1) ret.pop_back(); // just 1
  return ret;
}


z3::expr_vector BoolectorSolver::unsat_core() {
  // Since Boolector kind of by default returns multiple independent cores, we
  // just choose the smallest one and call that the core. failed_literals() is
  // sorted so we just pick the first one.
  z3::expr_vector ret(ctx_);
  auto cores = failed_literals();
  transform(cores[0].begin(), cores[0].end(), ExprVectorInserter(ret),
            [](auto&& node_pair) { return node_pair.z3_node(); });

  // vector<Z3BtorExprPair> all_trackers{fail_trackers_};
  // all_trackers.insert(all_trackers.end(), permanent_assumps_.begin(),
  //                     permanent_assumps_.end());
  // transform(assumptions_.begin(), assumptions_.end(),
  //           back_inserter(all_trackers),
  //           [](auto&& entry) { return entry.first; });

  // for (const auto& zbep : all_trackers) { 
  //   if (btor_solver()->isFailed(zbep.btor_node())) {
  //     ret.push_back(zbep.z3_node());
  //   }
  // }

  return ret;
}


z3::expr_vector BoolectorSolver::unsat_core_reasons() {
  z3::expr_vector reasons(ctx_);
  auto core = unsat_core();
  for (const auto& b : core) {
    reasons.push_back(GetTracked(b, b));
  }
  return reasons;
}


void BoolectorSolver::DumpBenchmark(
    std::ostream& out, size_t n, const z3::expr* assumptions) {
  fmt::print(out, "; dumped by BoolectorSolver\n");
  boost::optional<BtorWrapper> clone_opt;
  if (n) {
    // Converts z3::expr assumptions to boolector nodes
    vector<BoolectorNodeWrapper> assumptions_btor(n);
    transform(assumptions, assumptions + n, assumptions_btor.begin(),
              [&](auto&& a) { return this->rewriteAsBtor(a); });
    // The cloning of the BtorWrapper must be done after rewriting the
    // assumptions. I did this carefully in this order because if I clone after
    // rewriting, I'm sure the matchNode call below will work because the clone
    // will contain a copy of each assumption node.
    clone_opt = BtorWrapper(*btor_solver());
    for (auto& assumption : assumptions_btor) {
      clone_opt->Add(clone_opt->matchNode(assumption));
    }
  } else {
    clone_opt = BtorWrapper(*btor_solver());
  }
  assert(clone_opt);
  clone_opt->fixateAssumptions();
  clone_opt->DumpBenchmark(out);
}

std::ostream& BoolectorSolver::Print(std::ostream& os) const {
  (*solver_).Print(os);
  return os;
}

}


void mylog(const euforia::Z3BtorExprPair& n) {
  cerr << n.z3_node() << endl;
}

