// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_RMUS_H_
#define EUFORIA_RMUS_H_

#include "abstract_checker_impl.h"
#include "supp/expr_supp.h"

namespace euforia {
class TransitionSystem;

//! Refinement MUS. Turns a core into a MUS and generalizes it with equality
//! (or other simple) reasoning.
class RMus {
 public:

  using iterator = ExprSet::iterator;
  using const_iterator = ExprSet::const_iterator;

  RMus(const AbstractChecker::Impl& achk, const ExprSet& core);

  //! Returns true if this MUS is identically false
  bool is_false() const;

  z3::expr as_expr() const;

  z3::context& ctx() const { return achk_.ctx(); }

  size_t size() const { return mus_.size(); }

  iterator begin() { return mus_.begin(); }
  const_iterator begin() const { return mus_.begin(); }
  iterator end() { return mus_.end(); }
  const_iterator end() const { return mus_.end(); }

 private:
  const AbstractChecker::Impl& achk_;
  ExprSet mus_;

  void Generalize();
  void ValidateGeneralize(const ExprSet& original_mus,
                          const z3::expr& generalized_mus);
};

} // end namespace euforia

#endif
