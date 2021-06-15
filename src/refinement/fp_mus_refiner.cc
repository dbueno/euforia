// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "fp_mus_refiner.h"

#include <boost/range/combine.hpp>
#include <boost/algorithm/cxx11/copy_if.hpp>
#include <boost/range/adaptor/transformed.hpp>
#include <boost/range/algorithm/transform.hpp>

#include "supp/expr_supp.h"
#include "supp/equality_literal.h"
#include "refinement/fp_answer_scrubber.h"

using namespace euforia;

namespace euforia {

// Captures some info per fixedpoint rule that makes it possible for
// FpMusRefiner to produce an unsatisfiable subset.
struct FpMusRefiner::RuleInfo {
  RuleInfo(const z3::expr& head_app,
           const z3::expr& body_constraint,
           const ExprSubstitution& step_subst_inverse)
      : head_app(head_app), body_constraint(body_constraint),
        step_subst_inverse(step_subst_inverse) {}

  z3::expr head_app;
  z3::expr body_constraint;
  ExprSubstitution step_subst_inverse;
};

} // end namespace euforia

//^----------------------------------------------------------------------------^

namespace {
z3::expr_vector mk_init_vars(const z3::expr& p_app) {
  z3::expr_vector vars(p_app.ctx());
  boost::copy(ExprArgs(p_app), ExprVectorInserter(vars));
  return vars;
}


z3::expr input2expr(const PrimaryInput& pi) {
  return static_cast<const z3::expr&>(pi);
}

z3::expr var2current(const StateVar& v) { return v.current(); }
z3::expr var2next(const StateVar& v) { return v.next(); }

z3::expr_vector deep_copy(const z3::expr_vector& v) {
  z3::expr_vector ret(v.ctx());
  boost::copy(v, ExprVectorInserter(ret));
  return ret;
}


//^----------------------------------------------------------------------------^
//

//^----------------------------------------------------------------------------^


//! Represents the solution to an uninterpreted predicate
class Interpolant {
 public:
  //! \param fp_answer - conjunct from an fp.answer
  Interpolant(const z3::expr& fp_answer) 
      : rel_decl_(fp_answer.ctx()), rel_app_(fp_answer.ctx()),
        interpolant_quant_(fp_answer.ctx()) {
    // I'm assuming for the moment that the answer looks like this:
    //   (forall X. (= (relation X) <something>))
    // If <something> is true or false, no one cares
    // If <something> involves a quantified variable, it gets mapped back into
    // a state variable formula and returned.
    assert(fp_answer.is_forall());
    auto body = fp_answer.body();
    rel_app_ = body.arg(0);
    interpolant_quant_ = body.arg(1);
    rel_decl_ = rel_app_.decl();
  }

  z3::expr raw_interpolant() const { return interpolant_quant_; }

  bool is_false() const {
    return interpolant_quant_.is_app() && is_literal_false(interpolant_quant_);
  }
  bool is_true() const {
    return interpolant_quant_.is_app() && is_literal_true(interpolant_quant_);
  }
  z3::func_decl rel_decl() const { return rel_decl_; }
  z3::expr rel_app() const { return rel_app_; }

  z3::expr get_xsys_formula(const TransitionSystem& xsys,
                               bool use_next = false) const {
    auto project = mk_interpolant_projection(xsys, use_next);
    return project(interpolant_quant_);
  }

  ExprSubstitution
  mk_interpolant_projection(const TransitionSystem& cxsys,
                            bool use_next = false) const {
    auto rel = rel_app();
    ExprSubstitution subst(rel.ctx());
    // the relation element places are allocated using state variable enumeration
    auto vit = cxsys.vbegin(), vie = cxsys.vend();
    auto ait = ExprArgIterator::begin(rel), aie = ExprArgIterator::end(rel);
    for (; vit != vie && ait != aie; ++vit, ++ait) {
      const StateVar& v = *vit;
      const z3::expr& arg = *ait;
      subst.AddSubstitution(arg, use_next ? v.next() : v.current());
    }
    return subst;
  }

 private:
  z3::func_decl rel_decl_;
  z3::expr rel_app_;
  z3::expr interpolant_quant_;
};

//^----------------------------------------------------------------------------^

class InterpolantSet {
 public:
  InterpolantSet(z3::context& c,
                 const FuncDeclMap<FpMusRefiner::RuleInfo>& body2info) 
      : ctx_(c), body2info_(body2info) {
  }

  void SetAnswer(const z3::expr& fp_answer) {
    // I'm assuming the answer is a conjunction.
    for (const auto& e : ExprConjuncts(fp_answer)) {
      Add(Interpolant(e));
    }
  }

  void Add(const Interpolant& ipl) {
    if (ipl.is_false()) {
      falses_.push_back(ipl);
    } else {
      actuals_.push_back(ipl);
    }
    rel2ipl_.insert({ipl.rel_decl(), ipl});
  }

  z3::expr_vector get_xsys_unsat_cores(const TransitionSystem& xsys) const {
    z3::expr_vector ret(xsys.ctx());
    logger.Log(5, "InterpolantSet: creating xsys cores");
    for (const auto& p_k_ipl : actuals_) {
      ExprSet conjuncts;
      auto add_conjuncts = [&](const z3::expr& e) {
        boost::copy(ExprConjuncts(e), inserter(conjuncts, conjuncts.end()));
      };
      
      auto p_k_ipl_expr = p_k_ipl.get_xsys_formula(xsys);
      add_conjuncts(p_k_ipl_expr);
      logger.Log(5, "interpolant {}: {}", p_k_ipl.rel_decl().name(),
                 p_k_ipl_expr);
      // Rule info for (p-k & c => p-(k+1))
      if (auto search = body2info_.find(p_k_ipl.rel_decl());
          search != body2info_.end()) {
        const auto& rule_info = search->second;
        // Interpolant for p-(k+1)
        const auto& p_k_next_ipl = rel2ipl_.at(rule_info.head_app.decl());
        const auto& c = rule_info.body_constraint;
        const auto& invert_bmc_vars = rule_info.step_subst_inverse;
        // p_k_ipl & c & !p_k_next_ipl is UNSAT
        add_conjuncts(invert_bmc_vars(c));
        add_conjuncts(
            distribute_expr_not(p_k_next_ipl.get_xsys_formula(xsys, true)));
        logger.Log(5, "unsatisfiable subset from rule {} => {}: {}",
                   p_k_ipl.rel_decl().name(), p_k_next_ipl.rel_decl().name(),
                   conjuncts);
        ret.push_back(expr_mk_and(xsys.ctx(), conjuncts));
      }
    }
    assert(ret.size() != 0);
    return ret;
  }

  z3::context& ctx() const { return ctx_; }

  int64_t size() const { return actuals_.size(); }

 private:
  friend class FpMusRefiner;
  z3::context& ctx_;
  std::vector<Interpolant> falses_;
  std::vector<Interpolant> actuals_;
  FuncDeclMap<Interpolant> rel2ipl_;
  const FuncDeclMap<FpMusRefiner::RuleInfo>& body2info_;
};

} // end namespace

//^----------------------------------------------------------------------------^

namespace euforia {

//^----------------------------------------------------------------------------^

FpMusRefiner::FpMusRefiner(AbstractChecker::Impl& achk,
                           const std::shared_ptr<Solver>& s,
                           const std::vector<BmcStep>& steps,
                           z3::expr_vector bmc_core,
                           int64_t nr)
    : Refiner(achk, s, nr), fp_(achk.ctx()), core_(steps, bmc_core),
      body2info_(make_unique<FuncDeclMap<RuleInfo>>()) {
  z3::params fp_params(ctx());
  fp_params.set("engine", "spacer");
  // fp_params.set("validate", true);
  
  // disable inlining per Nikolaj: https://github.com/Z3Prover/z3/pull/1646
  fp_params.set("xform.inline_eager", false);
  fp_params.set("xform.inline_linear", false);
  fp_.set(fp_params);
    
  logger.Log(4, "fp mus refinement beginning with unsat core (size {})",
             core_.size());
  logger.LogFold(4, "{}", core_);
}

FpMusRefiner::~FpMusRefiner() = default;

//^----------------------------------------------------------------------------^

// Get spacer's answer from command line
// z3 -v:1 fp.engine=spacer fp.print_answer=true fp.xform.inline_eager=false fp.xform.inline_linear=false spacer_returns_bit2bool.smt2

// Entry point
z3::expr_vector FpMusRefiner::operator()() {
  logger.Log(3, "beginning fp interpolant search");
  z3::expr p_prev_app = mk_init_relation();
  auto init_rule = z3::forall(mk_init_vars(p_prev_app), p_prev_app);
  fp_.add_rule(init_rule, ctx().str_symbol("nought"));
  z3::func_decl p_prev = p_prev_app.decl();
  // XXX turn core into MUS

  int i = 1;
  for (auto it = core_.bmc_begin(), ie = core_.bmc_end(); it != ie;
       ++it, ++i) {
    const BmcUnsatStep& ustep = *it;
    p_prev_app = p_prev(ustep.current_vars());
    auto t = ustep.core_constraints();
    auto p_next_app = RegisterRelation(i, ustep); // predicate for next state
    AddRule(i, p_prev_app, t, p_next_app, ustep);
    p_prev = p_next_app.decl();
    p_prev_app = p_next_app; // for when loop exits
  }

  auto query = z3::exists(mk_init_vars(p_prev_app), p_prev_app);
  if (!LOG_DIR.empty()) {
    ofstream outfile(fmt::format("{}/ref{}-fp-bmc-core.smt2", LOG_DIR,
                                 num_refinements_+1));
    fmt::print(outfile, "{}\n", fp_);
    fmt::print(outfile, "(query {})\n", query);
  }

  auto result = fp_.query(query);
  if (result == z3::check_result::sat) {
    fmt::print("error\n");
    fmt::print("model: {}", fp_.get_answer());
  }
  assert(result != z3::check_result::sat);
  auto interpolant_formula = fp_.get_answer();
  logger.Log(5, "FpMusRefiner answer:\n{{{{{{{}}}}}}}", interpolant_formula);
  InterpolantSet ipls(ctx(), *body2info_);
  FpAnswerScrubber scrub;
  ipls.SetAnswer(scrub(interpolant_formula));
  logger.Log(3, "found {} interpolants from BMC", ipls.size());
  return ipls.get_xsys_unsat_cores(cxsys());
}

void FpMusRefiner::AddRule(int, const z3::expr& p_prev, const z3::expr&,
                           const z3::expr& p_i, const BmcUnsatStep& ustep) {
  auto rule = z3::forall(
      mk_rule_bound_vars(ustep, p_prev, p_i, ustep.core_constraints()),
      z3::implies(expr_and(p_prev, ustep.core_constraints()), p_i));
  auto rule_name =
      fmt::format("{} => {}", p_prev.decl().name().str(),
                  p_i.decl().name().str());
  fp_.add_rule(rule, ctx().str_symbol(rule_name.c_str()));
    
  RuleInfo rule_info(p_i, ustep.core_constraints(), ustep.subst().inverse());
  body2info_->insert({p_prev.decl(), rule_info});
}

// Creates p_i and returns  p_i applied to the right vars
z3::expr FpMusRefiner::RegisterRelation(int i, const BmcUnsatStep& ustep) {
  auto name = fmt::format("p-{}", i);
  z3::expr_vector vars = ustep.current_vars();
  if (ustep.has_transition()) {
    vars = ustep.next_vars();
  }
  z3::sort_vector sorts(ctx());
  boost::transform(vars, SortVectorInserter(sorts),
                   [&](const z3::expr& e) { return e.get_sort(); });
  auto p = ctx().function(name.c_str(), sorts, ctx().bool_sort());
  fp_.register_relation(p);
  return p(vars);
}


z3::expr_vector
FpMusRefiner::mk_rule_bound_vars(
    const BmcUnsatStep& ustep, const z3::expr&, const z3::expr&,
    const z3::expr&) const {
  ExprSet var_set;
  boost::copy(ustep.current_vars(), inserter(var_set, var_set.begin())); //ExprVectorInserter(ret));
  if (ustep.has_transition()) {
    boost::copy(ustep.input_vars(), inserter(var_set, var_set.begin()));
    boost::copy(ustep.next_vars(), inserter(var_set, var_set.begin()));
  }
  z3::expr_vector ret(ctx());
  boost::copy(var_set, ExprVectorInserter(ret));
  return ret;
}

z3::expr FpMusRefiner::mk_init_relation() {
  auto name = fmt::format("p-0");
  z3::expr_vector vars(ctx());
  boost::transform(cxsys().vars(), ExprVectorInserter(vars),
                   [](const StateVar& v) { return v.current(); });
  z3::sort_vector sorts(ctx());
  boost::transform(vars, SortVectorInserter(sorts),
                   [&](const z3::expr& e) { return e.get_sort(); });
  auto p = ctx().function(name.c_str(), sorts, ctx().bool_sort());
  fp_.register_relation(p);
  return p(vars);
}




//^----------------------------------------------------------------------------^
BmcUnsat::BmcUnsat(const std::vector<BmcStep>& steps,
                   z3::expr_vector core)
    : core_(core.begin(), core.end()), ctx_(core.ctx()) {
  for (const auto& step : steps) {
    steps_.push_back(BmcUnsatStep(*this, step));
  }
}
  
BmcUnsatIterator BmcUnsat::bmc_begin() const {
  return BmcUnsatIterator(steps_.begin());
}

BmcUnsatIterator BmcUnsat::bmc_end() const {
  return BmcUnsatIterator(steps_.end());
}

inline bool BmcUnsat::contains(const z3::expr& e) const {
  return core_.find(e) != core_.end();
}

std::ostream& operator<<(std::ostream& out, const BmcUnsat& bmc_core) {
  for (auto it = bmc_core.bmc_begin(), ie = bmc_core.bmc_end(); it != ie;
       ++it) {
    fmt::print(out, "{}", *it);
  }
  return out;
}

//^----------------------------------------------------------------------------^
  
BmcUnsatStep::BmcUnsatStep(const BmcUnsat& u, const BmcStep& s) 
    : core_(u), step_(s) {}

z3::expr BmcUnsatStep::core_constraints() const {
  z3::expr_vector v(core_.ctx());
  boost::algorithm::copy_if(
      step_.constraints(), ExprVectorInserter(v),
      [&](const z3::expr& e) -> bool { return core_.contains(e); });
  auto ret = expr_mk_and(v);
  return ret;
}

ExprSubstitution BmcUnsatStep::subst() const {
  return step_.subst();
}

z3::expr_vector BmcUnsatStep::current_vars() const {
  return step_.current_vars();
}

z3::expr_vector BmcUnsatStep::next_vars() const {
  return step_.next_vars();
}

z3::expr_vector BmcUnsatStep::input_vars() const {
  return step_.input_vars();
}

std::ostream& operator<<(std::ostream& out, const BmcUnsatStep& step) {
  fmt::print(out, "bmc step {} constraints\n", step.state_index());
  fmt::print(out, "{}\n", step.core_constraints());
  return out;
}

} // end namespace euforia
