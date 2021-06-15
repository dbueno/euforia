// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "xsys/vmt_transition_system.h"

#include <algorithm>
#include <list>
#include <llvm/ADT/EquivalenceClasses.h>
#include <mathsat.h>
#include <random>
#include <stdexcept>
#include <string>

#include "checker_types.h"
#include "supp/equality_literal.h"
#include "supp/euforia_config.h"
#include "supp/expr_dot_formatter.h"
#include "supp/expr_iterators.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_supp.h"
#include "supp/mathsat_supp.h"
#include "supp/mathsat_vmt_parser.h"
#include "xsys/var_info_traversal.h"


using namespace std;
using namespace llvm;


namespace euforia {
using namespace vmt;

//*----------------------------------------------------------------------------*

struct VmtTransitionSystem::Stats {
  const VmtTransitionSystem& xsys;

  int64_t num_bv_vars;
  int64_t num_array_vars;
  int64_t num_bv_inputs;
  int64_t num_array_inputs;
  
  Stats(const VmtTransitionSystem& xsys)
    : xsys(xsys), num_bv_vars(0), num_array_vars(0), num_bv_inputs(0),
      num_array_inputs(0) {}

  inline void Print(std::ostream& os) const;

};

void VmtTransitionSystem::Stats::Print(std::ostream& os) const {
#define PRINT_STAT(n) fmt::print(os, "{}: {}\n", #n, n)

  PRINT_STAT(num_bv_vars);
  PRINT_STAT(num_bv_inputs);
  PRINT_STAT(num_array_vars);
  PRINT_STAT(num_array_inputs);

#undef PRINT_STAT
}

//^----------------------------------------------------------------------------^

class VmtTransitionSystem::Impl {
 public:
  unordered_set<std::string> decl_names_;
  
  VmtTransitionSystem& xsys_;
  z3::expr init_;     // def that is annotated with :init
  z3::expr trans_;    // def that is annotated with :trans
  z3::expr property_; // def that is annotated with :invar-property
  // Background assertions can be used for under-approximation or for eagerly
  // feeding lemmas to the abstract search. Lemmas are typically so obviously
  // valid in QF_AUFBV that Mathsat parses the term as 'true', because of
  // simple rewriting; 'true' doesn't make for a very useful lemma. To get
  // around this, lemmas should be existentials, annotated with :background,
  // and the variables will be instantiated in order according to the terms
  // found in formulas annotated with :background-arg1, :background-arg2, etc.
  z3::expr background_;
  mathsat::Z3TermRewriter msat_to_z3;

  Impl(VmtTransitionSystem& ts)
    : ctx_(ts.ctx()), ts_(ts), init_(ts.ctx()), trans_(ts.ctx()),
      property_(ts.ctx()), background_(ts.ctx()), xsys_(ts), stats_(ts),
      msat_to_z3(ts.ctx()) {}
  Impl(const Impl&) = delete;
  Impl& operator=(const Impl&) = delete;


  void TranslateAst(MathsatVmtAst& ast) {
    logger.Log(3, "translating VMT AST into transition system");
    TermWrapper init, trans, prop, background;
    vector<TermWrapper> background_args;
    msat_term *terms = ast.terms;
    char **annots = ast.annots;
    size_t n = ast.n;
    

    auto getidx = [](char *v) -> int {
      std::istringstream tmp(v);
      int ret;
      if (!(tmp >> ret)) {
        ret = -1;
      }
      return ret;
    };

    for (size_t i = 0; i < n; ++i) {
      std::string key(annots[2*i]);
      msat_term t = terms[i];
      if (key == "init") {
        init = t;
      } else if (key == "trans") {
        trans = t;
      } else if (key == "invar-property") {
        int idx = getidx(annots[2*i+1]);
        if (idx < 0) {
          logger.Log(1, "invalid property index {}", annots[2*i+1]);
          throw runtime_error("bad property index (see log)");
        } else if (idx == 0) { // 0 is default property index
          prop = t;
        }
      } else if (key == "next") {
        std::string val(annots[2*i+1]);
        if (val.length() && val[0] == '|') {
          val = val.substr(1, val.length()-2);
        }
        msat_decl d = msat_find_decl(ast.env, val.c_str());
        if (MSAT_ERROR_DECL(d)) {
          d = msat_declare_function(ast.env, val.c_str(),
                                    msat_term_get_type(terms[i]));
        }
        msat_term msat_next = msat_make_constant(ast.env, d);
        auto current = msat_to_z3(mathsat::TermWrapper(ast.env, t));
        auto next = msat_to_z3(mathsat::TermWrapper(ast.env, msat_next));
        /*const auto& var = */ts_.AddVar(MakeStateVar(current, next));
      } else if (key == "background") {
        background = t;
      } else if (key == "background-arg") {
        int idx = getidx(annots[2*i+1]);
        background_args.resize(idx+1, TermWrapper(ast.env, msat_make_true(ast.env)));
        background_args[idx] = t;
      }
    }

    if (init.is_error()) {
      throw std::runtime_error(":init not found");
    }
    if (trans.is_error()) {
      throw std::runtime_error(":trans not found");
    }
    if (prop.is_error()) {
      throw std::runtime_error(":invar-property not found");
    }

    ts_.ip_.init({});

    logger.Log(3, "rewriting transition relation into z3");
    init_ = msat_to_z3(mathsat::TermWrapper(ast.env, init));
    trans_= msat_to_z3(mathsat::TermWrapper(ast.env, trans));
    property_ = msat_to_z3(mathsat::TermWrapper(ast.env, prop));
    if (!background.is_error()) {
      background_ = msat_to_z3(
          mathsat::TermWrapper(ast.env, background)).simplify();
      if (!background_args.empty()) {
        z3::expr_vector dst(background_.ctx());
        // reverse args because z3 expects this I think
        std::reverse(background_args.begin(), background_args.end());
        for (auto&& e : background_args) {
          dst.push_back(msat_to_z3(e));
        }
        auto body = background_.body();
        background_ = body.substitute(dst);
      }
      logger.Log(3, "found background assertion in vmt file");
      logger.Log(4, "{}", background_);
    }

    auto add_inputs = [&](const z3::expr& e) {
      if (e.num_args() == 0) {
        if (!ts_.FindVar(e) && !IsValue(e)) {
          auto name = e.decl().name().str();
          ts_.AddInput(MakeInput(e));
        }
      }
    };
    // XXX uhh was I even thinking here, there are no inputs supposed to be in the initial state?????
    // XXX CHANGE_AFTER_FMCAD
    for_each(po_expr_iterator::begin(init_), po_expr_iterator::end(init_),
             add_inputs);
    for_each(po_expr_iterator::begin(trans_), po_expr_iterator::end(trans_),
             add_inputs);
    // XXX no inputs in the property please
    for_each(po_expr_iterator::begin(property_),
             po_expr_iterator::end(property_), add_inputs);
    // XXX insert a check that init is defined over X, property over X, and T over (X, X', Y)
    VarInfoTraversal var_info(ts_);
    var_info.Reset();
    var_info.Traverse(init_);
    var_info.Traverse(property_);
    if (false && (!var_info.vars_defd().empty() ||
        !var_info.inputs_used().empty())) {
      fmt::print(cerr, "error: :init or :invar-property has next-state vars or inputs\n");
      for (const auto& v : var_info.inputs_used()) {
        fmt::print(cerr, "{}", v);
      }
      exit(1);
    }
    var_info.Reset();
  }

  void collect_static_statistics(Statistics *st) const;

 private:
  friend VmtTransitionSystem;
  z3::context& ctx_;
  VmtTransitionSystem& ts_;
  Stats stats_;
  
};

void
VmtTransitionSystem::Impl::collect_static_statistics(Statistics *st) const {
#define PRINT_STAT(v) st->Update(#v, stats_.v)
  PRINT_STAT(num_bv_vars);
  PRINT_STAT(num_bv_inputs);
  PRINT_STAT(num_array_vars);
  PRINT_STAT(num_array_inputs);
#undef PRINT_STAT
  msat_to_z3.collect_statistics(st);
}

//*----------------------------------------------------------------------------*
//VmtTransitionSystem

VmtTransitionSystem::VmtTransitionSystem(vmt::MathsatVmtAst& ast,
                                         z3::context& ctx_in)
  : TransitionSystem(ctx_in),
    pimpl_(std::make_unique<Impl>(*this)), trans_(ctx_in), background_(ctx_in) {

  pimpl_->TranslateAst(ast);
  init_state_ = pimpl_->init_;
  trans_ = pimpl_->trans_;
  property_ = pimpl_->property_;
  background_ = pimpl_->background_;
  if (bool(background_) && (background_.is_true() || background_.is_false() || !background_.is_bool())) {
    throw runtime_error(fmt::format("bad background assertion in vmt: {}",
                                    background_));
  } 
  
  logger.Log(3, "parsed transition relation");
  logger.Log(4, "{}", trans_);

  for (const auto& sv : vars()) {
    switch (sv.current().get_sort().sort_kind()) {
      case Z3_BV_SORT:
        pimpl_->stats_.num_bv_vars++;
        break;

      case Z3_ARRAY_SORT:
        pimpl_->stats_.num_array_vars++;
        break;
        
      default:
        // logger.Log(0, "sv {} has sort {}", sv, sv.current().get_sort());
        break;
    }
  }

  for (const auto& inp : inputs()) {
    switch (inp.z.get_sort().sort_kind()) {
      case Z3_BV_SORT:
        pimpl_->stats_.num_bv_inputs++;
        break;

      case Z3_ARRAY_SORT:
        pimpl_->stats_.num_array_inputs++;
        break;

      default:
        // logger.Log(0, "input {} has sort {}", inp, inp.z.get_sort());
        break;
    }
  }
}

VmtTransitionSystem::VmtTransitionSystem(z3::context& ctx) 
    : TransitionSystem(ctx), pimpl_(std::make_unique<Impl>(*this)),
      trans_(ctx), background_(ctx) {}


VmtTransitionSystem::VmtTransitionSystem(const VmtTransitionSystem& other)
  : TransitionSystem(other), trans_(other.trans_),
    trans_clauses_(other.trans_clauses_), background_(other.background_),
    pimpl_(std::make_unique<Impl>(*this)) {
}

VmtTransitionSystem::VmtTransitionSystem(VmtTransitionSystem&& other)
    : TransitionSystem(other), trans_(other.trans_.ctx()),
      background_(other.background_.ctx()), pimpl_(std::make_unique<Impl>(*this)) {
  swap(trans_, other.trans_);
  swap(trans_clauses_, other.trans_clauses_);
  swap(background_, other.background_);
}

VmtTransitionSystem::~VmtTransitionSystem() = default;

const char *VmtTransitionSystem::solver_logic() const {
  return "QF_ABV";
}
  
void VmtTransitionSystem::AddInitialStateToChecker(Solver& s) const {
  s.Add(init_state());
}
  
// NB this is not called during refinement. Instead, the relevant parts of T
// are computed on the fly.
void VmtTransitionSystem::AddTransitionsToChecker(Solver& s) const {
  AddOneHots(s);
  s.Add(trans());
  s.Add(background_);
}

void VmtTransitionSystem::AddOneHots(Solver& LC) const {
//    auto oneHots = accumulate(begin(joinPointOneHots), end(joinPointOneHots), ctx().bool_val(true), expr_and);
  auto oneHotsCurr = ip_repr().current().constraintsAtMost();
  auto oneHots = accumulate(oneHotsCurr.begin(), oneHotsCurr.end(), ctx().bool_val(true), expr_and);
  if (!z3::eq(oneHots, ctx().bool_val(true)))
    LC.Add(oneHots);
  auto oneHotsNext = ip_repr().next().constraintsAtMost();
  oneHots = accumulate(oneHotsNext.begin(), oneHotsNext.end(), ctx().bool_val(true), expr_and);
  if (!z3::eq(oneHots, ctx().bool_val(true)))
    LC.Add(oneHots);
}
  
void VmtTransitionSystem::AddStateUpdates(Solver& s) const {
  s.Add(trans());
}


std::shared_ptr<AbstractModel>
VmtTransitionSystem::ExpandedPreimage(CheckerSat&, const std::shared_ptr<Model>&, const Cube&, Cube&, std::shared_ptr<TSlice> *) const {
  abort();
}

std::ostream& VmtTransitionSystem::Print(std::ostream& os) const {
  TransitionSystem::Print(os);
  pimpl_->stats_.Print(os);
  fmt::print(os, "T:\n");
  fmt::print(os, "{}\n", trans());
  if (background_) {
    fmt::print(os, "T background assertion:\n");
    fmt::print(os, "{}\n", background_);
  }
  if (!LOG_DIR.empty()) {
    ofstream f(LOG_DIR + "/trans.dot");
    ExprDotFormatter format(f);
    format.Print({trans()});
  }
  return os;
}

  
//*-------------------------------------------------------------------------------*
//rewriter

void VmtTransitionSystem::RewriteSystem(
    const std::function<z3::expr(const z3::expr&)>& rewrite) {
  init_state_ = rewrite(init_state_);
  property_ = rewrite(property_);
  trans_ = rewrite(trans_);
  for (int i = 0; i < static_cast<int>(trans_clauses_.size()); i++) {
    trans_clauses_[i] = rewrite(trans_clauses_[i]);
  }
  if (background_) {
    background_ = rewrite(background_);
  }
  // crashes the compiler:
  //for (auto& [k, v] : trans_defs_copy) {}
}


void VmtTransitionSystem::collect_static_statistics(Statistics *st) const {
  pimpl_->collect_static_statistics(st);
}

}

