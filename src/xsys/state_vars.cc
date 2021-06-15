// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "xsys/state_vars.h"

#include <llvm/Support/Casting.h>

#include "supp/expr_set_traversal.h"
#include "supp/expr_supp.h"


using namespace std;
using namespace llvm;
  
namespace euforia {
  
  inline std::string func_decl_string(const z3::expr& e) {
    const char *str = Z3_func_decl_to_string(e.ctx(), e.decl());
    std::string s(str);
    assert(s.data() != str);
    return s;
  }

  ostream& StateVar::Print(ostream& os) const {
    os << "StateVar<" << name_ << ":" << func_decl_string(zcurr_) << "/" <<
        func_decl_string(znext_) << ">";
    return os;
  }
  
  bool StateVar::is_term() const {
    return isa<TermStateVar>(*this) || isa<TermArrayStateVar>(*this);
  }
  
  
  ArrayStateVar::ArrayStateVar(std::string name, z3::expr zcurr, z3::expr znext) : StateVar(name, zcurr, znext, kind::kArray) {
    assert(zcurr.is_array());
    assert(z3::eq(zcurr.get_sort().array_domain(), znext.get_sort().array_domain()));
    assert(z3::eq(zcurr.get_sort().array_range(), znext.get_sort().array_range()));
  }
  
  z3::expr ArrayStateVar::getUninitVersion() const {
    return ctx().constant(("uninit-" + name()).c_str(), current().get_sort());
  }
  
  


  TermArrayStateVar::TermArrayStateVar(std::string name, z3::expr zcurr, z3::expr znext) : StateVar(name, zcurr, znext, kind::TermArray) {
    assert(zcurr.is_array());
    assert(z3::eq(zcurr.get_sort().array_domain(), znext.get_sort().array_domain()));
    assert(z3::eq(zcurr.get_sort().array_range(), znext.get_sort().array_range()));
  }


  
  

std::unique_ptr<StateVar> MakeStateVar(const z3::expr& zcurr,
                                       const z3::expr& znext) {
  assert(zcurr.decl().kind() == znext.decl().kind());
  unique_ptr<StateVar> ret;
  if (zcurr.is_array()) {
    ret = std::make_unique<ArrayStateVar>(
        zcurr.decl().name().str(), zcurr, znext);
  } else {
    ret = std::make_unique<PlainStateVar>(
        zcurr.decl().name().str(), zcurr, znext);
  }
  return ret;
}

}

