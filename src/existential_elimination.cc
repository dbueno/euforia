// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "existential_elimination.h"

#include "abstract_model.h"
#include "supp/equality_literal.h"
#include "supp/expr_set_traversal.h"
#include "supp/expr_substitution.h"
#include "supp/model_justifier.h"
#include "supp/z3_solver.h"
#include "supp/fmt_supp.h"
#include "xsys/var_info_traversal.h"

#include <numeric>
#include <list>

using namespace std;
using namespace llvm;

namespace euforia {

std::ostream& operator<<(std::ostream& out,
                         const ExistentialElimination::Config& c) {
  switch (c) {
    case ExistentialElimination::Config::kExact:
      fmt::print(out, "kExact");
      break;
    case ExistentialElimination::Config::kBestEffort:
      fmt::print(out, "kBestEffort");
      break;
  }
  return out;
}

}


namespace euforia {


//^----------------------------------------------------------------------------^
//EqualityResolver

// a term is ground if it's not a var to eliminate and all of its children are
// ground
bool EqualityResolver::IsGround(const z3::expr& e) {
  if (auto search = vars_to_eliminate_.find(e);
      search != vars_to_eliminate_.end()) {
    return false;
  }

  for (unsigned i = 0; i < e.num_args(); i++) {
    if (!IsGround(e.arg(i))) {
      return false;
    }
  }

  return true;
}

boost::optional<z3::expr> EqualityResolver::ResolveExpr(const z3::expr& expr) {
  if (IsGround(expr)) {
    // ground terms resolve to themselves
    return expr;
  } else if (expr.num_args() > 0) {
    // complex terms may be able to be resolved recursively
    z3::expr_vector new_args(ctx());
    for (unsigned i = 0; i < expr.num_args(); i++) {
      if (auto subresolve = ResolveExpr(expr.arg(i))) {
        new_args.push_back(*subresolve);
      } else {
        return boost::none;
      }
    }
    return expr.decl()(new_args);
  } else {
    return ResolveTermRec(expr);
  }
}

// Resolve the variable e to a ground term we can use in a lemma
boost::optional<z3::expr> EqualityResolver::ResolveTermRec(const z3::expr& var) {
  // This procedure could be more efficient if all terms are resolved at once.
  // Basically, use a queue of vars. If you need to recursively resolve, leave
  // the var on the queue and go onte the next. When a literal is resolved, pop
  // it off the queue. If something has already been resolved, you can look it
  // up in the cache.
  
  if (implied_equalities_.findValue(var) == implied_equalities_.end()) {
    return boost::none;
  }
  // find ground terms that we can resolve to and other terms we can't (but
  // those other terms may still be resolvable)
  ExprSet ground_terms, other_terms;
  for (auto it = implied_equalities_.findLeader(var),
       ie = implied_equalities_.member_end(); it != ie; ++it) {
    const z3::expr& term = *it;
    if (IsGround(term)) {
      ground_terms.insert(term);
    } else {
      other_terms.insert(term);
    }
  }
  logger.Log(5, "term {} can resolve to {} ground terms: {}", var,
             ground_terms.size(), ground_terms);
#if 0
  for (const z3::expr& term : ground_terms) {
     prefer state variable to constant
    if (cts_.hasStateVar(term))
      return Optional<z3::expr>(term);
     prefer expression to constant
    if (term.num_args() > 0)
      return Optional<z3::expr>(term);
  }
#endif
  if (!ground_terms.empty()) {
    boost::optional<z3::expr> ret(*ground_terms.begin());
    for (auto& term : ground_terms) {
      if (IsUConstant(term)) {
        ret = term;
        break;
      }
    }
    // choose arbitrarily if we didn't find a preference
    return ret;
  }

  if (Push(var)) {
    logger.Log(5, "considering {} other terms for resolving {}: {}",
               other_terms.size(), var, other_terms);
    for (const z3::expr& term : other_terms) {
      if (term.num_args() == 0)
        continue;
      // i'm handling the case where there is a constraint var = (F a Y2) (i.e.
      // var has (F a Y2) in its equivalence class), var is not *directly*
      // resolvable, where Y1 and Y2 are inputs. var resolves to (F a Y2) if and
      // only if Y2 is resolvable (assume that a is ground). So we have a
      // recursive case below.

      if (auto resolved_term = ResolveExpr(term))
        return resolved_term;
    }
  }

  return boost::none;
}

//*----------------------------------------------------------------------------*
//DnfIterator
//
// XXX make a caching evaluating model that doesn't depend on a transition system (between AbstractModel and z3::model)

//! Produces a DNF for a formula f_ by repeatedly asking the solver for a
//model, extracting a cube, then asserting the negation of that cube to find
//another cube.
class DnfIterator { // InputIterator
  boost::optional<z3::ExprWrapper> f_;
  std::unique_ptr<Z3Solver> solver_;
  CheckResult result_;
  std::list<z3::expr> negated_cubes_;
  
  ExprSet cube_;
 public:
  DnfIterator(const z3::expr& f, const char *logic = nullptr) 
      : f_(f),
        solver_(std::make_unique<Z3Solver>(f.ctx(),
                                           logic ? logic : "QF_AUFBV")) {
    solver_->Add(f);
    result_ = solver_->Check();
  }
  
  DnfIterator() : result_(CheckResult::kUnsat) {}

  z3::context& ctx() { return solver_->ctx(); }

  bool operator==(const DnfIterator& other) {
    // any unsat results are the same
    if (result_ == CheckResult::kUnsat)
      return result_ == other.result_;
    
    // if sat, make sure the same problem was solved
    return result_ == other.result_ &&
        f_ == other.f_ &&
        negated_cubes_ == other.negated_cubes_;
  }
  bool operator!=(const DnfIterator& other) {
    return !(*this == other);
  }

  ExprSet operator*() {
    if (cube_.empty()) {
      assert(result_ == CheckResult::kSat);
      cube_ = ExtractCube();
    }
    return cube_;
  }

  DnfIterator& operator++() {
    z3::expr cube_negation(ctx());
    std::transform(cube_.begin(), cube_.end(), ExprOrInserter(cube_negation),
                   expr_not);
    cube_.clear();
    negated_cubes_.push_front(cube_negation);
    solver_->Add(cube_negation);
    result_ = solver_->Check();
    assert(result_ != CheckResult::kUnknown);
    return *this;
  }

  ExprSet ExtractCube() {
    logger.LogOpenFold(5, "justifying DnfIterator model to get a cube");
    ExprSet predicates;
    auto model = solver_->get_model();
    ModelJustifier justify([&](const z3::expr& e, bool c) {
                           return model->Eval(e, c); });
    auto assertions = solver_->assertions();
    justify.ComputePredicates(begin(assertions), end(assertions), &predicates);
    // XXX ideally, once I know how z3 ctx simplification works, run it here on predicates
    logger.LogCloseFold(5, "");
    return predicates;
  }
};

class RemoveNestedEqualities 
    : public ExprRewriter<RemoveNestedEqualities>,
    public ExprVisitor<RemoveNestedEqualities, z3::expr> {
  const EquivalenceClasses<z3::ExprWrapper>& classes_;

 public:
  RemoveNestedEqualities(const EquivalenceClasses<z3::ExprWrapper>& classes)
  : classes_(classes) {}

  template <typename InputIt, typename OutputIt>
  void operator()(InputIt it, InputIt ie, OutputIt io) {
    transform(it, ie, io, [&](const z3::expr& c) { return Rewrite(c); });
  }

  ExprSet operator()(const ExprSet& conjuncts) {
    ExprSet output;
    (*this)(conjuncts.begin(), conjuncts.end(), inserter(output, output.end()));
    return output;
  }

  z3::expr Rewrite(const z3::expr& e) {
    auto e_new = ExprRewriter::Rewrite(e);
    if (!z3::eq(e, e_new))
      logger.Log(5, "nested equality removal turned {} into {}", e, e_new);
    return e_new;
  }

  bool VarIs(const z3::expr& e, const z3::expr& target) {
    return any_of(classes_.findLeader(e), classes_.member_end(),
                  [&](const z3::expr& e) { return z3::eq(e, target); });
  }

  bool VarIsTrue(const z3::expr& e) { return VarIs(e, e.ctx().bool_val(true)); }
  bool VarIsFalse(const z3::expr& e) {
    return VarIs(e, e.ctx().bool_val(false));
  }

  z3::expr visitExpr(const z3::expr& e) {
    return e.decl()(NewArgsExprVector(e));
  }

  // (= x (f a b)) & x <-> x & (f a b)
  z3::expr visitEQ(const z3::expr& e) {
    z3::expr ret = e.decl()(NewArgsExprVector(e));
    auto k0 = Arg(e, 0), k1 = Arg(e, 1);
    if (k0.num_args() > 0) {
      swap(k0, k1);
    }
    // k0 is 0-arg if anything is
    if (k0.is_bool() && k0.num_args() == 0) {
      if (VarIsTrue(k0)) {
        ret = k1;
      } else if (VarIsFalse(k0)) {
        ret = expr_not(k1);
      }
    }
    return ret;
  }
};

//*----------------------------------------------------------------------------*
//ExistentialElimination::Impl

class ExistentialElimination::Impl {
 public:

};

//*----------------------------------------------------------------------------*
//ExistentialElimination

ExistentialElimination::ExistentialElimination(z3::context& c, Config cfg) :
    ctx_(c), pimpl_(std::make_unique<ExistentialElimination::Impl>()), cfg_(cfg) {}

ExistentialElimination::~ExistentialElimination() = default;


ExprSet ExistentialElimination::ElimCube(
    const ExprSet& vars_to_eliminate_in, const ExprSet& literals) {
  logger.LogOpenFold(4, "performing conjunctive existential elimination ({})", cfg_);
  for (auto& lit : literals) {
    if (!IsLiteral(lit)) {
      ostringstream ss;
      ss << lit;
      EUFORIA_FATAL("non-literal in literals list: " + ss.str());
    }
  }
  // restrict vars_to_eliminate with those occurring in literals
  auto vars_to_eliminate(vars_to_eliminate_in);
  ExprSetTraversal expr_info(vars_to_eliminate);
  expr_info.Traverse(literals.begin(), literals.end());
  for (auto it = vars_to_eliminate.begin(); it != vars_to_eliminate.end();
       /* in body */) {
    if (expr_info.matches().find(*it) == expr_info.matches().end()) {
      it = vars_to_eliminate.erase(it);
    } else {
      ++it;
    }
  }
  logger.Log(5, "vars to eliminate that occur in literals: {}",
             vars_to_eliminate);

  if (vars_to_eliminate.empty()) {
    return literals;
  }
  
  EquivalenceClasses<z3::ExprWrapper> implied_equalities;
  GatherImpliedEqualities(literals.begin(), literals.end(),
                          &implied_equalities);

  // 1. for each v in vars_to_eliminate, find resolve it to a term t
  // 2. substitute t for v in each literal
  // 3. return substituted conjunction

  // 1. ...
  EqualityResolver resolver(ctx(), vars_to_eliminate, implied_equalities);
  ExprSubstitution elim_substitution(ctx());
  for (auto& v : vars_to_eliminate) {
    auto maybe_term = resolver.ResolveTerm(v);
    if (maybe_term) {
      logger.Log(4, "resolving {} to {}", v, *maybe_term);
      elim_substitution.AddSubstitution(v, *maybe_term);
    }
  }
  
  // 2. ...
  vector<z3::ExprWrapper> ret_vec;
  std::transform(literals.begin(), literals.end(), std::back_inserter(ret_vec),
                 elim_substitution);
  ret_vec.erase(std::remove_if(ret_vec.begin(), ret_vec.end(), is_literal_true), ret_vec.end());

  // check
  if (elim_substitution.size() != vars_to_eliminate.size()) {
    ExprSet missed_vars = vars_to_eliminate;
    for (const z3::expr& v : elim_substitution.src()) {
      missed_vars.erase(v);
    }
    logger.Log(5, "ExistentialElimination substitution: {}", elim_substitution);
    logger.Log(5, "    missed vars: {}", missed_vars);
  
    if (cfg_ == Config::kExact) {
      z3::expr_vector vars(ctx());
      copy(vars_to_eliminate.begin(), vars_to_eliminate.end(),
           ExprVectorInserter(vars));
      z3::expr body(ctx());
      copy(ret_vec.begin(), ret_vec.end(), ExprAndInserter(body));
      auto ex_formula = z3::exists(vars, body);
      logger.Log(5, "ex_farmula {}", ex_formula);
      auto simplifier = z3::tactic(ctx(), "qe") &
          z3::repeat(z3::tactic(ctx(), "ctx-simplify")) &
          z3::tactic(ctx(), "simplify");
      z3::goal g(ctx());
      g.add(ex_formula);
      logger.Log(3, "goal: {}", g);
      auto new_goals = simplifier(g);
      logger.Log(3, "apply_result: {}", new_goals);
      ExprSet ret;
      for (unsigned i = 0; i < new_goals.size(); i++) {
        logger.Log(3, "is_decided_sat {}: {}", 0, new_goals[i].is_decided_sat());
        logger.Log(3, "as_expr {}: {}", 0, new_goals[i].as_expr());
        ret.insert(new_goals[i].as_expr());
      }
      return ret;
      //for (unsigned i = 0; i < new_goals.size(); i++) {
      //  logger.Log(3, "new goal {} {}", i, new_goals[i]);
      //}
      EUFORIA_FATAL("need to implement the case where I under-approximate the existential eliminiation to catch missed_vars");
    }
  }

  // 3. ...
  logger.LogCloseFold(4, "performing conjunctive existential elimination - done");
  return ExprSet(ret_vec.begin(), ret_vec.end());
}

//*----------------------------------------------------------------------------*
// general elimination

z3::expr ExistentialElimination::Elim(const ExprSet& vars_to_eliminate,
                                      const z3::expr& f) {
  logger.Log(4, "performing {} existential elimination", cfg_);
  logger.LogOpenFold(4, "formula:");
  logger.LogCloseFold(4, "{}", f);
  if (cfg_ == Config::kBestEffort) {
    // do some simple simplifications to try to flatten formula
    auto cube = FlattenIntoLiterals(f);
    auto cube_elimd  = ElimCube(vars_to_eliminate, cube);
    z3::expr cube_expr(ctx());
    copy(cube_elimd.begin(), cube_elimd.end(), ExprAndInserter(cube_expr));
    logger.Log(4, "existential elimination done");
    return cube_expr;
  }

  z3::expr f_eliminated(ctx());
  
#if 1
  auto output = ExprAndInserter(f_eliminated);
  z3::expr_vector vars(ctx());
  copy(vars_to_eliminate.begin(), vars_to_eliminate.end(),
       ExprVectorInserter(vars));
  auto ex_formula = z3::exists(vars, f);
  auto simplifier = z3::tactic(ctx(), "qe") &
      z3::repeat(z3::tactic(ctx(), "ctx-simplify")) &
      z3::tactic(ctx(), "simplify");
  z3::goal qe_goal(ctx());
  qe_goal.add(ex_formula);
  auto new_goals = simplifier(qe_goal);
  for (unsigned i = 0; i < new_goals.size(); i++) {
    *output++ = new_goals[i].as_expr();
  }
#else
  // Iterate over the disjunctive normal form of f, then eliminate each cube
  auto output = ExprOrInserter(f_eliminated);
  int count = 0;
  for (auto it = DnfIterator(f), ie = DnfIterator(); it != ie; ++it) {
    auto cube = *it;
    logger.Log(5, "DNF cube {}: {}", ++count, cube);
    auto cube_elimd = ElimCube(vars_to_eliminate, cube);
    z3::expr cube_expr(ctx());
    copy(cube_elimd.begin(), cube_elimd.end(), ExprAndInserter(cube_expr));
    *output++ = cube_expr;
  }
#endif
  logger.Log(4, "performing general existential elimination - done");
  return output.Get();
}

//^----------------------------------------------------------------------------^
// outher methods

ExprSet ExistentialElimination::FlattenIntoLiterals(const z3::expr& e) {
  EquivalenceClasses<z3::ExprWrapper> implied_equalities;
  GatherImpliedEqualities(ExprConjunctIterator::begin(e), ExprConjunctIterator::end(),
                          &implied_equalities);
  // use equalities to flatten
  RemoveNestedEqualities flatten(implied_equalities);
  ExprSet output;
  flatten(ExprConjunctIterator::begin(e), ExprConjunctIterator::end(),
          inserter(output, output.end()));
  return output;
}


void ExistentialElimination::AddImpliedEquality(
    const z3::expr& lit,
    EquivalenceClasses<z3::ExprWrapper> *implied_equalities) {
  if (EqualityLiteral::is_equality(lit)) {
    EqualityLiteral eq_lit(lit);
    implied_equalities->unionSets(eq_lit.lhs(), eq_lit.rhs());
  }
}

}
