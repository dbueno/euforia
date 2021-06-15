// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef expr_dot_fmt_hpp
#define expr_dot_fmt_hpp

#include <ostream>
#include <propagate_const.h>

#include "checker_types.h"
#include "supp/expr_supp.h"

namespace euforia {
class ExprDotFormatter {
 public:
  ExprDotFormatter(std::ostream& os);
  ~ExprDotFormatter();

  // print a set of expressions
  void Print(const ExprSet& exprs);

 private:
  class Impl;
  std::experimental::propagate_const< // const-forwarding pointer wrapper
    std::unique_ptr<Impl>> pimpl_;
};
}

#endif /* expr_dot_fmt_hpp */
