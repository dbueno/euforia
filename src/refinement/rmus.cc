// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "rmus.h"

#include <boost/range/algorithm/copy.hpp>
#include <sstream>
#include <llvm/ADT/EquivalenceClasses.h>

#include "abstract_checker_impl.h"
#include "existential_elimination.h"
#include "supp/euforia_config.h"
#include "supp/marco.h"
#include "supp/fmt_supp.h"
#include "xsys/var_info_traversal.h"

namespace euforia {

RMus::RMus(const AbstractChecker::Impl& ac, const ExprSet& core)
    : achk_(ac) {
  // extracts an MUS from the core
  const bool use_marco = true;
  logger.Log(4, "RMus start with core:");
  logger.LogFold(4, "{}", core);
  if (use_marco) {
    TimerDuration marco_d(0);
    ScopedTimeKeeper marco_time(&marco_d);
    shared_ptr<Solver> solver = achk_.make_solver();               // safe and good
#ifdef NDEBUG
    if (auto boolector = dynamic_pointer_cast<BoolectorSolver>(solver)) {
      boolector->SetOption(BTOR_OPT_MODEL_GEN, 0); // no need for models
    }
#endif
    marco::MarcoEnumerator marco_enum(*solver, core);
    auto marco_core = *marco_enum.begin(); // gets the first MUS only
    assert(marco_core.kind() == marco::MarcoEnumerator::Supremals::kMus);
    mus_ = ExprSet(marco_core.begin(), marco_core.end());
    logger.Log(4, "RMus after marco:");
    logger.LogFold(4, "{}", mus_);
  }

  Generalize();
}


// The mus is unsat. I want to do some cheap simplification, in particular
// taking top-level Booleans and equalities and substituting them away if
// possible. Doesn't matter if it doesn't always work.
void RMus::Generalize() {
  logger.Log(4, "generalizing MUS with equality reasoning");
  EquivalenceClasses<z3::ExprWrapper> implied_equalities;
  ExistentialElimination::GatherImpliedEqualities(
      mus_.begin(), mus_.end(), &implied_equalities);
  VarInfoTraversal info(achk_.cxsys());
  info.Traverse(mus_.begin(), mus_.end());
  ExprSet vars_to_eliminate(info.inputs_used().begin(),
                            info.inputs_used().end());
  if (!euforia_config.use_osbmc_slicing) {
    // Note GENERALIZE_WITH_SLICING: Slicing currently conflicts with
    // eliminating Boolean state vars. At the very least, this is because a
    // lemma may be (a & !a), sensitizing the search to the Boolean variable a.
    // I will address this in a different way in the future because otherwise
    // the search will likely just get stuck trying to sensitize to all the
    // Boolean vars. eliminates Boolean state vars, just not others
    auto is_bool = [](const z3::expr& e) { return e.is_bool(); };
    copy_if(info.vars_defd().begin(), info.vars_defd().end(), 
            inserter(vars_to_eliminate, vars_to_eliminate.end()), is_bool);
  }
  // let's leave the other vars in and see....
  //vars_to_eliminate.insert(info.vars_used_.begin(), info.vars_used_.end());
  //vars_to_eliminate.insert(info.vars_defd_.begin(), info.vars_defd_.end());
  EqualityResolver resolver(ctx(), vars_to_eliminate, implied_equalities);
  ExprSubstitution elim_substitution(ctx());
  for (auto& var : vars_to_eliminate) {
    if (auto maybe_term = resolver.ResolveTerm(var)) {
      elim_substitution.AddSubstitution(var, *maybe_term);
    }
  }
  z3::expr_vector mus_generalized(ctx());
  transform(mus_.begin(), mus_.end(), ExprVectorInserter(mus_generalized),
            elim_substitution);
#ifdef EXPENSIVECHECKS
  ValidateGeneralize(mus_, expr_mk_and(mus_generalized));
#endif
  mus_.clear();
  boost::copy(mus_generalized, std::inserter(mus_, mus_.begin()));
  logger.Log(4, "MUS generalized: {}", mus_generalized);
  logger.Log(4, "generalizing MUS with equality reasoning - done");
}
  
bool RMus::is_false() const {
  // contains "false"
  if (auto search = mus_.find(ctx().bool_val(false)); search != mus_.end()) {
    return true;
  }
  // contains elt and !elt -- this conflicts with slicing because we may need
  // predicate sensitization. see GENERALIZE_WITH_SLICING comment above
  if (!euforia_config.use_osbmc_slicing) {
    for (const auto& elt : mus_) {
      if (auto search = mus_.find(expr_not(elt)); search != mus_.end()) {
        return true;
      }
    }
  }
  return false;
}

z3::expr RMus::as_expr() const {
  return expr_mk_and(ctx(), mus_);
}

void RMus::ValidateGeneralize(
    const ExprSet& mus, const z3::expr& mus_generalized) {
  const auto& cxsys_ = achk_.cxsys();
  z3::solver s(cxsys_.ctx());
  z3::expr mus_formula(cxsys_.ctx());
  copy(mus.begin(), mus.end(), ExprAndInserter(mus_formula));
  s.add(mus_formula);
  s.add(!mus_generalized);
  if (z3::check_result::sat == s.check()) {
    fmt::print(cerr, "mus formula:\n{}\n", mus_formula);
    fmt::print(cerr, "mus generalized:\n{}\n", mus_generalized);
    fmt::print(cerr, "state variable assignments:\n");
    auto model = s.get_model();
    for (auto it = cxsys_.vbegin(), ie = cxsys_.vend(); it != ie; ++it) {
      const StateVar& v = *it;
      fmt::print(cerr, "  {} -> +: {} -> {}\n", v.current(),
                 model.eval(v.current()), model.eval(v.next()));
    }
    EUFORIA_FATAL("ValidateGeneralizeMus failed: original mus does not imply the generalized one, means generalized is wrong");
  }
}

} // end namespace euforia
