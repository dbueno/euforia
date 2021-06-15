// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/yices_supp.h"
#include "supp/wrapstream.h"

using euforia::yices_supp::TermWrapper;
using euforia::yices_supp::TypeWrapper;


namespace euforia {
namespace yices_supp {
std::ostream& operator<<(std::ostream& os, const TermWrapper& t) {
  auto *file = wrapostream(os);
  yices_pp_term(file, t, 100, INT_MAX, 0);
  return os;
}

std::ostream& operator<<(std::ostream& os, const TypeWrapper& t) {
  auto *file = wrapostream(os);
  yices_pp_type(file, t, 100, INT_MAX, 0);
  return os;
}
} // namespace yices_supp
} // namespace euforia

void mylog(const TermWrapper& t) {
  fmt::print(std::cerr, "{}\n", t);
}

void mylog(const TypeWrapper& t) {
  fmt::print(std::cerr, "{}\n", t);
}
