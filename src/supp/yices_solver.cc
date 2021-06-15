// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/yices_solver.h"

#include <yices.h>
#include <gmpxx.h>

#include "supp/expr_rewriter.h"
#include "supp/std_supp.h"
#include "supp/wrapstream.h"
#include "supp/yices_supp.h"



//^----------------------------------------------------------------------------^

using namespace std;


namespace euforia {
namespace yices_supp {
  
//^----------------------------------------------------------------------------^

class Solver::Impl {
 public:
  context_t *ctx_;
  // helpers for conversion to yices formulas
  int32_t const_index_;
  ExprMap<term_t> consts_;
  std::vector<z3::expr> consts_by_index_;
  Z3ToYicesRewriter to_yices_;
  YicesToZ3Rewriter to_z3_;

  Impl(z3::context& c, const char *logic)
      : const_index_(0), to_yices_(const_index_, consts_, consts_by_index_),
        to_z3_(c, consts_by_index_) {
    auto config = yices_new_config();
    auto r = yices_default_config_for_logic(config, logic);
    assert(r == 0);
    ctx_ = yices_new_context(config);
    yices_free_config(config);
  }

  operator context_t*() { return ctx_; }
};

//^----------------------------------------------------------------------------^

class Model::Impl {
 public:
  Impl(z3::context&) {}
};

//^----------------------------------------------------------------------------^

Model::Model(Solver& s)
    : solver_(s), m_(yices_get_model(*s.pimpl_, 1), yices_free_model),
      pimpl_(std::make_unique<Impl>(s.ctx())) {}

Model::~Model() = default;

z3::expr Model::Eval(const z3::expr& e, bool) const {
  logger.Log(5, "yices_supp::Model eval {}", e);
  auto t = solver_.MapConcreteExpr(e);
  auto val = yices_get_value_as_term(m_.get(), t.yices_node());
  if (val == NULL_TERM) {
    throw std::runtime_error(yices_error_string());
  }
  logger.Log(5, "yices const_index {}", solver_.pimpl_->const_index_);
  logger.Log(5, "yices constants {}", solver_.pimpl_->consts_by_index_.size());
  return solver_.pimpl_->to_z3_(val);
}

std::ostream& Model::Print(std::ostream& os) const {
  auto *file = wrapostream(os);
  yices_print_model(file, m_.get());
  fclose(file);
  return os;
}

//^----------------------------------------------------------------------------^

Solver::Solver(z3::context& z3_ctx, const char *logic, bool)
    : pimpl_(std::make_unique<Solver::Impl>(z3_ctx, logic)), z3_ctx_(z3_ctx),
      assertions_(z3_ctx)
  {}

Solver::~Solver() = default;

void Solver::Push() {
  if (-1 == yices_push(*pimpl_)) {
    throw std::exception(); // XXX have a message
  }
}

void Solver::Pop() {
  if (-1 == yices_pop(*pimpl_)) {
    throw std::exception(); // XXX have a message
  }
}

void Solver::Add(const z3::expr& e) {
  assertions_.push_back(e);
  auto p = pimpl_->to_yices_(e);
  yices_assert_formula(*pimpl_, p.yices_node());
  yices_to_z3_.insert({p.yices_node(), e});
}

CheckResult Solver::Check() {
  yices_to_z3_.clear();
  return TranslateResult(yices_check_context(*pimpl_, NULL));
}

CheckResult Solver::Check(const ExprSet& assumptions) {
  yices_to_z3_.clear();
  fmt::print(cerr, "yices::Check set\n");
  vector<term_t> t;
  for (auto& a : assumptions) {
    t.push_back(pimpl_->to_yices_(a).yices_node());
    yices_to_z3_.insert({t.back(), a});
  }
  return TranslateResult(yices_check_context_with_assumptions(
          *pimpl_, NULL, t.size(), t.data()));
}

CheckResult Solver::Check(const std::vector<z3::expr>& assumptions) {
  yices_to_z3_.clear();
  fmt::print(cerr, "yices::Check\n");
  vector<term_t> t;
  for (auto& a : assumptions) {
    t.push_back(pimpl_->to_yices_(a).yices_node());
    yices_to_z3_.insert({t.back(), a});
  }
  return TranslateResult(yices_check_context_with_assumptions(
          *pimpl_, NULL, t.size(), t.data()));
}

CheckResult Solver::TranslateResult(smt_status_t r) {
  switch (r) {
    case STATUS_SAT:     return CheckResult::kSat;
    case STATUS_UNSAT:   return CheckResult::kUnsat;
    case STATUS_UNKNOWN: return CheckResult::kUnknown;
    default:
      EUFORIA_FATAL("TranslateResult : cannot translate result");
      return CheckResult::kUnknown;
  }
}

std::shared_ptr<euforia::Model> Solver::get_model() {
  return std::make_shared<Model>(*this);
}

z3::expr_vector Solver::unsat_core() {
  z3::expr_vector ev(z3_ctx_);
  term_vector_t v;
  yices_init_term_vector(&v);
  auto r = yices_get_unsat_core(*pimpl_, &v);
  if (-1 == r || CTX_INVALID_OPERATION == r)  {
    throw std::exception();
  }
  for (unsigned i = 0; i < v.size; i++) {
    ev.push_back(yices_to_z3_.at(v.data[i]));
  }
  yices_delete_term_vector(&v);
  return ev;
}

//denis check this XXX
z3::expr_vector Solver::unsat_core_reasons() {
  z3::expr_vector reasons(z3_ctx_);
  auto core = unsat_core();
  for (const auto& b : core) {
    reasons.push_back(GetTracked(b, b));
  }
  return reasons;
}

std::ostream& Solver::Print(std::ostream& os) const {
  term_vector_t v;
  yices_init_term_vector(&v);

  auto *file = wrapostream(os);

  for (auto a : assertions_) {
    yices_pp_term(file, pimpl_->to_yices_(a).yices_node(), 80, 1, 10);
  }
  //dump(file, *pimpl_);
  fclose(file);
  yices_delete_term_vector(&v);
  return os;
}

Z3YicesExprPair Solver::MapConcreteExpr(const z3::expr& e) {
  return pimpl_->to_yices_(e);
}

YicesToZ3Rewriter& Solver::yices_to_z3() {
  return pimpl_->to_z3_;
}

Z3ToYicesRewriter& Solver::z3_to_yices() {
  return pimpl_->to_yices_;
}

} // end namespace yices
} // end namespace euforia

