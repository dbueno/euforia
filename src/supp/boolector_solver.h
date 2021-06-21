// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef btor_concretizing_solver_hpp
#define btor_concretizing_solver_hpp

#include "supp/boolector_supp.h"
#include "checker_types.h"
#include "hashcons.h"
#include "supp/std_supp.h"
#include "supp/solver.h"

#include "z3++.h"

#include <boost/container_hash/hash_fwd.hpp>
#include <boost/optional/optional.hpp>
#include <memory>

namespace euforia {
using BtorCompleteAssignment = std::unordered_map<std::string,
      std::shared_ptr<boolector::BtorAssignment>>;

// mapping z3 (concrete) into boolector isn't 1-1, so we keep track of the mapping in pairs
class Z3BtorExprPair {
 public:
  Z3BtorExprPair(const z3::expr& c, const boolector::BoolectorNodeWrapper& n)
      : z3_node_(c), btor_node_(n) {
    assert(bool(z3_node()));
    assert(!btor_node().is_null());
  }

  inline const z3::expr& z3_node() const { return z3_node_; }
  inline void set_z3_node(const z3::expr& c) { z3_node_ = c; assert(bool(c)); }
  inline const boolector::BoolectorNodeWrapper& btor_node() const {
    return btor_node_;
  }
  inline void set_btor_node(const boolector::BoolectorNodeWrapper& n_in) {
    btor_node_ = n_in;
    assert(!btor_node_.is_null());
  }
  
  
  inline bool operator==(const Z3BtorExprPair& other) const {
    return z3::eq(z3_node_, other.z3_node_) &&
        boolector::eq(btor_node_, other.btor_node_);
  }

  inline bool operator!=(const Z3BtorExprPair& other) const {
    return !(*this == other);
  }
  
  std::size_t hash() const;

 private:
  // z3 concrete node
  z3::expr z3_node_;
  // boolector concretization
  boolector::BoolectorNodeWrapper btor_node_;

};

struct HashZ3BtorExprPair {
  inline std::size_t operator()(const Z3BtorExprPair& p) const {
    return p.hash();
  }
};

struct EqualToZ3BtorExprPair {
  inline bool operator()(const Z3BtorExprPair& p1,
                         const Z3BtorExprPair& p2) const {
    return p1 == p2;
  }
};

std::size_t hash_value(const Z3BtorExprPair&);


/*----------------------------------------------------------------------------*/

class BoolectorSolver;

class BoolectorModel : public Model {
 public:
  BoolectorModel(BoolectorSolver& s) : solver_(s) {}
  virtual ~BoolectorModel() = default;

  virtual z3::expr Eval(const z3::expr& e, bool completion = false) override;
  virtual std::ostream& Print(std::ostream&) const override;
  virtual pp::DocPtr Pp() const override {
    // XXX fix this
    std::stringstream ss;
    Print(ss);
    return pp::text(ss.str());
  }
  virtual void collect_statistics(Statistics *st) const override;

 private:
  BoolectorSolver& solver_;
  ExprMap<z3::expr> queried_;
};

// the add() method will rewrite the z3 expr as boolector in order to add it
// to the boolector solver
class BoolectorSolver : public Solver {
 public:
  explicit BoolectorSolver(z3::context&);
  virtual ~BoolectorSolver() override = default;
  //! Does a clone of the underlying BtorWrapper and resets basically
  //! everything else.
  BoolectorSolver(const BoolectorSolver&);

  std::unique_ptr<BoolectorSolver> clone() const;
  
  // XXX this is deprecated and discourage
  inline const std::shared_ptr<boolector::BtorWrapper>& btor_solver() const {
    return solver_;
  }

  void SetOption(BtorOption o, uint32_t val) {
    btor_solver()->setOption(o, val);
  }

  virtual inline z3::context& ctx() const override { return ctx_; }
  
  virtual CheckResult Check(
      const size_t n, const z3::expr* assumptions) override;
  using Solver::Check;
  virtual void Push() override;
  virtual void Pop() override;
  virtual std::shared_ptr<Model> get_model() override;
  virtual std::shared_ptr<Model> get_model(const z3::expr_vector& vars) override;
  virtual z3::expr_vector unsat_core() override;
  virtual z3::expr_vector unsat_core_reasons() override;
  virtual z3::expr_vector assertions() const override {
    EUFORIA_FATAL("assertions() is not supported");
  }
  virtual std::string reason_unknown() const override {
    EUFORIA_FATAL("reason_unknown() is not supported");
  }
  virtual std::ostream& Print(std::ostream& os) const override;

  boolector::BtorWrapper::result BtorCheck(bool printAssertions = false);
  
  virtual void Add(const z3::expr& z3Conc) override;
  
  //! If is_permanent is true, adds the assumptions to be internally permanent.
  //! This means they can participate in cores. If is_permanent is false,
  //! behaves the same as Add(z3_conc).
  void AddGeneral(const z3::expr& z3_conc, bool is_permanent);
  //void Add(const boolector::BoolectorNodeWrapper& n);
  

  virtual void DumpBenchmark(
      std::ostream& os, size_t n, const z3::expr* assumptions) override;
  using Solver::DumpBenchmark;

 private:
  friend class BoolectorModel;
  // assumptions sent to the next check()
  std::unordered_map<Z3BtorExprPair, std::shared_ptr<std::string>,
      HashZ3BtorExprPair, EqualToZ3BtorExprPair> assumptions_;
  z3::context& ctx_;
  std::vector<Z3BtorExprPair> fail_trackers_; // index into assumptions
  // permanent assumptions that are never cleared
  // used to track state updates and aux equations in a way that lets
  // us get the core
  std::vector<Z3BtorExprPair> permanent_assumps_;
  bool adds_to_perm_assumps_ = false; // if true, add() will put assumps here
  std::vector<std::shared_ptr<boolector::BtorWrapper> > solver_stack_;
  std::shared_ptr<boolector::BtorWrapper> solver_;
  boolector::Z3ToBtorRewriter z3_to_btor_;
  
  boolector::BoolectorNodeWrapper rewriteAsBtor(const z3::expr& z3Conc) {
    return z3_to_btor_.Rewrite(z3Conc);
  }
  
  Z3BtorExprPair MapConcreteExpr(const z3::expr& e);
  
  boolector::BoolectorNodeWrapper Assume(
      const Z3BtorExprPair& n, bool track = false,
      const boost::optional<std::string>& tag = boost::none);

  std::string GetAssumptionLabel(const Z3BtorExprPair&) const;
  
  void Unassume(const Z3BtorExprPair& n);
  
  const std::unordered_map<Z3BtorExprPair, std::shared_ptr<std::string>,
      HashZ3BtorExprPair, EqualToZ3BtorExprPair>& assumptions() const {
    return assumptions_;
  }

  void ClearAssumptions();

  std::vector<std::vector<Z3BtorExprPair>> failed_literals();
 
  const std::vector<Z3BtorExprPair>& fail_trackers() const {
    return fail_trackers_;
  }
  
  std::vector<ExprSet> FindMuses(const bool multiple = false);

  CheckResult TranslateResult(boolector::BtorWrapper::result r) {
    switch (r) {
      case boolector::BtorWrapper::result::kSat: return CheckResult::kSat;
      case boolector::BtorWrapper::result::kUnsat: return CheckResult::kUnsat;
      case boolector::BtorWrapper::result::kUnknown: return CheckResult::kUnknown;
    }
    EUFORIA_FATAL("you had only three jobs...");
  }
  
  virtual const char *version() const override {
    return "BoolectorSolver";
  }
};


}

void mylog(const euforia::Z3BtorExprPair& n);

#endif /* btor_concretizing_solver_hpp */
