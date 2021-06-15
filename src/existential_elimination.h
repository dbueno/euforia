// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef existential_elimination_hpp
#define existential_elimination_hpp

#include "checker_types.h"
#include "supp/expr_supp.h"
#include "xsys/cyclic_traversal.h"

#include <boost/optional/optional.hpp>
#include <propagate_const.h>
#include <llvm/ADT/EquivalenceClasses.h>

namespace euforia {

template <typename T>
std::ostream& operator<<(std::ostream& out,
                        const llvm::EquivalenceClasses<T>& classes) {
  fmt::print(out, "EquivalenceClasses ({} classes):\n",
             classes.getNumClasses());
  for (auto class_it = classes.begin(), class_ie = classes.end();
       class_it != class_ie; ++class_it) {
    if (!class_it->isLeader())
      continue;
    fmt::print(out, "leader: {}\n", class_it->getData());
    for (auto it = classes.member_begin(class_it), ie = classes.member_end();
         it != ie; ++it) {
      const z3::expr e = *it;
      fmt::print(out, "    {}\n", e);
    }
  }
  return out;
}

//*----------------------------------------------------------------------------*
//EqualityResolver

class EqualityResolver : public CyclicTraversal {
 public:
  EqualityResolver(
      z3::context& c, const ExprSet& vars_to_eliminate,
      const llvm::EquivalenceClasses<z3::ExprWrapper>& implied_equalities)
      : ctx_(c), vars_to_eliminate_(vars_to_eliminate),
      implied_equalities_(implied_equalities) {}

  z3::context& ctx() { return ctx_; }

  //! Attempt to resolve e to a ground term using equality reasoning
  boost::optional<z3::expr> ResolveTerm(const z3::expr& e) {
    ResetTraversal();
    return ResolveTermRec(e);
  }

 private:
  z3::context& ctx_;
  const ExprSet& vars_to_eliminate_;
  const llvm::EquivalenceClasses<z3::ExprWrapper>& implied_equalities_;

  boost::optional<z3::expr> ResolveExpr(const z3::expr& expr);
  boost::optional<z3::expr> ResolveTermRec(const z3::expr&);

  bool IsGround(const z3::expr&);
};

//^----------------------------------------------------------------------------^
//ExistentialElimination

/// Existential elimination for a conjunction of literals only
class ExistentialElimination {
 public:
  enum class Config {
    //! Fails if it can't eliminate anything in vars_to_eliminate, may return
    //false if you call it on unsat f ormulas
    kExact = 0,

    //! May return a formula that doesn't eliminate some variables. Doesn't
    // call the solver to try to eliminate variables. Can be called on
    // unsatisfiable formulas as a way of generalizing them.
    kBestEffort,
  };
 
  ExistentialElimination(z3::context&, Config c = Config::kExact);
  ~ExistentialElimination();

  z3::context& ctx() { return ctx_; }

  //! Eliminates vars from the conjunction of the given literals.
  ExprSet ElimCube(const ExprSet& vars_to_eliminate,
                     const ExprSet& literals);

  //! Eliminates vars from the given formula
  z3::expr Elim(const ExprSet& vars_to_eliminate, const z3::expr& e);


  //! Flatten e into a list of literals (accounting for x & (x = (y = z)) in
  //the input)
  ExprSet FlattenIntoLiterals(const z3::expr& e);

  //! Output classes of terms that are definitely equivalent using only
  //equalities and Booleans
  template <typename InputIt>
  static void GatherImpliedEqualities(
      InputIt it, InputIt ie,
      llvm::EquivalenceClasses<z3::ExprWrapper> *implied_equalities) {
    for (; it != ie; ++it) {
      AddImpliedEquality(*it, implied_equalities);
    }

    logger.LogOpenFold(4, "found {} equivalence classes",
                       implied_equalities->getNumClasses());
    if (logger.ShouldLog(4)) {
      std::ostringstream os;
      os << *implied_equalities;
      logger.LogCloseFold(4, "{}", os.str()); // XXX just use fmt diroctly
    }
  }

  //! If lit implies an equality, add it to output
  static void AddImpliedEquality(
      const z3::expr& lit,
      llvm::EquivalenceClasses<z3::ExprWrapper> *implied_equalities);

 private:
  z3::context& ctx_;
  Config cfg_;
  class Impl;
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;


};

}

#endif
