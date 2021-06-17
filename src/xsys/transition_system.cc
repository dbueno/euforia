// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "xsys/transition_system.h"

#include <llvm/Support/Casting.h>
#include <stdexcept>

#include "cube.h"
#include "supp/cube_insert_iterator.h"
#include "supp/expr_dot_formatter.h"
#include "supp/expr_iterators.h"
#include "supp/expr_supp.h"
#include "supp/solver.h"
#include "supp/statistics.h"


namespace euforia {

using namespace std;
using llvm::isa;
using llvm::dyn_cast;
using llvm::cast;

//// TRANSITION SYSTEM


TransitionSystem::TransitionSystem(z3::context& ctx) 
    : ctx_(ctx), simplify_params_(ctx), init_state_(ctx.bool_val(true)),
    property_(ctx.bool_val(true)), ip_(ctx) {
  simplify_params_.set("expand_select_store", true);
  simplify_params_.set("hi_div0", true);
    
}

TransitionSystem::TransitionSystem(const TransitionSystem& other) 
    : ctx_(other.ctx_), simplify_params_(other.simplify_params_),
    // vars changed so prime_ and unprime_ get initialized
    vars_changed_(true), inputs_(other.inputs_),
    expr2input_(other.expr2input_), vars_(other.vars_),
    expr2var_(other.expr2var_),
    prime_(nullptr), unprime_(nullptr),
    ip_(other.ip_), init_state_(other.init_state_), property_(other.property_) {
}

TransitionSystem::TransitionSystem(TransitionSystem&& other) 
    : ctx_(other.ctx_), simplify_params_(other.simplify_params_),
    vars_changed_(other.vars_changed_),
    init_state_(other.init_state_), property_(other.property_),
    ip_(other.ctx_) {
  swap(inputs_, other.inputs_);
  swap(expr2input_, other.expr2input_);
  swap(vars_, other.vars_);
  swap(expr2var_, other.expr2var_);
  swap(prime_, other.prime_);
  swap(unprime_, other.unprime_);
  swap(ip_, other.ip_);
}

bool TransitionSystem::IsControlLocation(const z3::expr& e) const {
  if (auto v = FindVar(e)) {
    return v->is_location();
  }
  return false;
}

bool TransitionSystem::IsLocation(const z3::expr& e) const {
  if (auto v = FindVar(e)) {
    return v->is_location_not_wait();
  }
  return false;
}



const StateVar& TransitionSystem::AddVar(unique_ptr<StateVar> var) {
  const StateVar& ret = *var.get();
  auto inserted = expr2var_.insert({ret.current(), ref(ret)}).second;
  if (!inserted)
    throw std::runtime_error("duplicate state var: " + ret.name());
  inserted = expr2var_.insert({ret.next(), ref(ret)}).second;
  if (!inserted)
    throw std::runtime_error("duplicate state var: " + ret.name());
  vars_[var->name()] = move(var);
  //vars_.insert({var->name, move(var)}); // why doesn't this work?!
  vars_changed_ = true;
  logger.Log(5, "added var {} to transition system", ret.name());
  return ret;
}

const PrimaryInput& TransitionSystem::AddInput(unique_ptr<PrimaryInput> inp) {
  const PrimaryInput& ret = *inp.get();
  auto inserted = expr2input_.insert({ret.z, ref(ret)}).second;
  if (!inserted)
    throw std::runtime_error("duplicate input: " + ret.name);
  inputs_[inp->name] = move(inp);
  vars_changed_ = true;
  return ret;
}
  
  
void TransitionSystem::DeleteVar(const std::string& name) {
  prime_.reset();
  unprime_.reset();
  auto& v = *vars_.at(name);
  logger.Log(kLogLowest, "deleting: {}", v);
  expr2var_.erase(v.current());
  expr2var_.erase(v.next());
  vars_.erase(v.name());
  vars_changed_ = true;
}


void TransitionSystem::DeleteInput(const std::string& name) {
  logger.Log(kLogLowest, "deleting: {}", inputs_.at(name));
  inputs_.erase(name);
  vars_changed_ = true;
}


bool TransitionSystem::is_trans_formula(const z3::expr& e) const {
  for (auto I = po_expr_iterator::begin(e), E = po_expr_iterator::end(e);
       I != E; ++I) {
    auto x = *I;
    if (x.is_const()) {
      if (FindVar(x) || FindInput(x) || IsTerm0(x) || x.is_numeral() ||
          x.is_true() || x.is_false())
        continue;
      logger.Log(0, "const that shouldn't be here: {}", x);
      return false;
    }
  }
  return true;
}

void TransitionSystem::Prepare() {
  if (vars_changed_) {
    prime_ = std::make_unique<CachingExprSubstitution>(ctx());
    unprime_ = std::make_unique<CachingExprSubstitution>(ctx());
    for (auto& [name, var] : vars_) {
      (void)name;
      prime_->AddSubstitution(var->current(), var->next());
      unprime_->AddSubstitution(var->next(), var->current());
    }
    vars_changed_ = false;
  }
}


z3::expr TransitionSystem::prime(const z3::expr& e_in) const {
  assert(!vars_changed_);
  return (*prime_)(e_in);
}

z3::expr TransitionSystem::unprime(const z3::expr& e_in) const {
  assert(!vars_changed_);
  return (*unprime_)(e_in);
}


ostream& TransitionSystem::Print(ostream& os) const {
  os << "state variables (" << vars_.size() << "):" << endl;
  for (const auto& p : vars_) {
    os << "  " << *p.second << endl;
  }
  os << "primary inputs (" << inputs_.size() << "):" << endl;
  for (const auto& p : inputs_) {
    os << "  " << *p.second << endl;
  }
  os << "location variables:"  << endl;
  ip_.print(os);

  unsigned i = 1;
  int num_conjuncts =
      count_if(ExprConjunctIterator::begin(init_state_),
               ExprConjunctIterator::end(),
               [](auto&&) { return true; });
  fmt::print(os, "initial state ({} conjuncts):\n", num_conjuncts);
  for (auto& elt : ExprConjuncts(init_state_)) {
    fmt::print(os, "{}. {}\n", i++, elt);
  }
  if (!LOG_DIR.empty()) {
    ofstream f(LOG_DIR + "/init_state.dot");
    ExprDotFormatter format(f);
    format.Print({init_state_});
  }
  num_conjuncts = 
      count_if(ExprConjunctIterator::begin(property_),
               ExprConjunctIterator::end(),
               [](auto&&) { return true; });
  fmt::print(os, "property ({} conjuncts):\n", num_conjuncts);
  for (auto& elt : ExprConjuncts(property_)) {
    fmt::print(os, "{}. {}\n", i++, elt);
  }
  if (!LOG_DIR.empty()) {
    ofstream f(LOG_DIR + "/init_state.dot");
    ExprDotFormatter format(f);
    format.Print({init_state_});
  }
  return os;
}
  


void TransitionSystem::AddOneHots(Solver& LC) const {
//    auto oneHots = accumulate(begin(joinPointOneHots), end(joinPointOneHots), ctx().bool_val(true), expr_and);
  auto oneHotsCurr = ip_.current().constraintsAtMost();
  auto oneHots = accumulate(oneHotsCurr.begin(), oneHotsCurr.end(),
                            ctx().bool_val(true), expr_and);
  if (!z3::eq(oneHots, ctx().bool_val(true)))
    LC.Add(oneHots);
  auto oneHotsNext = ip_.next().constraintsAtMost();
  oneHots = accumulate(oneHotsNext.begin(), oneHotsNext.end(),
                       ctx().bool_val(true), expr_and);
  if (!z3::eq(oneHots, ctx().bool_val(true)))
    LC.Add(oneHots);
}





void TransitionSystem::SimplifyPreimage(Cube& z) const {
  // TODO push this simplification down into abstract_stg
  struct SimplifyEufConstants
      : public ExprRewriter<SimplifyEufConstants>,
      public ExprVisitor<SimplifyEufConstants, z3::expr> {
    z3::expr visitExpr(const z3::expr& e) { return e.decl()(NewArgsExprVector(e)); }
    z3::expr visitNOT(const z3::expr& e) {
      switch(e.arg(0).decl().decl_kind()) {
        case Z3_OP_EQ: {
          auto arg0 = Arg(e,0).arg(0), arg1 = Arg(e,0).arg(1);
          if (IsUConstant(arg0) && IsUConstant(arg1)) {
            return e.ctx().bool_val(true);
          }
          else
            return visitExpr(e);
          break;
        }
          
        default:
          return visitExpr(e);
      }
    }
    z3::expr visitDISTINCT(const z3::expr& e) {
      for (unsigned i = 0; i < e.num_args(); i++) {
        if (!IsUConstant(Arg(e,i))) {
          return visitExpr(e);
        }
      }
      return e.ctx().bool_val(true);
    }
  } SimpEUFConst;
  
  
  // remove !@L-... and (distinct K1 K2 ... Kn)
  auto zit = z.begin();
  while (zit != z.end()) {
    auto lit = *zit;
    if (is_not(lit)) {
      size_t ID;
      if (ip_.getID(lit.arg(0), ID)) {
        zit = zit.erase();
        continue;
      }
    }
    
    auto newlit = SimpEUFConst.Rewrite(lit);
    if (!z3::eq(lit, newlit)) { // rewritten
      if (is_literal_true(newlit)) {
        zit = zit.erase();
        continue;
      } else {
        zit.replace(newlit, prime(newlit));
      }
    }
    ++zit;
  }
}


std::shared_ptr<AbstractModel>
TransitionSystem::GetModel(const shared_ptr<Model>& m) const {
  return std::make_shared<AbstractModel>(m, *this);
}

CubeInsertIterator TransitionSystem::cube_inserter(Cube& c) const {
  return CubeInsertIterator(*this, c);
}


void TransitionSystem::collect_static_statistics(Statistics *st) const {
#define updcast(v,t) st->Update(#v, static_cast<int64_t>(t))
  updcast(num_state_vars, num_vars());
  updcast(num_inputs, num_inputs());
#undef updcast
}
  
    
} // namespace euforia

