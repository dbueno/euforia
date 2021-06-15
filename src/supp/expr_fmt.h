// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_EXPR_FMT_H_
#define EUFORIA_SUPP_EXPR_FMT_H_

#include <fmt/format.h>
#include <fmt/ostream.h>
#include <sstream>
#include <z3++.h>

#include "supp/expr_iterators.h"

namespace euforia {
//! Prints expressions using their hashes and their decl names and uses a
//! visited set so we don't print anything twice
class ExprLegend {
 public:
  //! Prints a single node
  std::ostream& PrintNode(std::ostream& os, const z3::expr& e) {
    std::stringstream ss;
    for (const auto& a : ExprArgs(e)) {
      fmt::print(ss, "{:08x} ", a.hash());
    }
    fmt::print(os, "{:08x}: {} {}\n", e.hash(), e.decl().name().str(),
               ss.str());
    return os;
  }

  //!  Prints an expression and all its descendents in post order
  std::ostream& Print(std::ostream& os, const z3::expr& e) {
    for (auto it = po_expr_ext_iterator::begin(e, visited_),
         ie = po_expr_ext_iterator::end(e, visited_); it != ie; ++it) {
      PrintNode(os, *it);
    }
    return os;
  }

  inline void Reset() {
    visited_.clear();
  }

 private:
  ExprSet visited_;
};
} // end namespace euforia

#endif
