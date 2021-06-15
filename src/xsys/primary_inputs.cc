// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "xsys/primary_inputs.h"

#include <iostream>
#include <llvm/Support/Casting.h>

#include "abstract_model.h"
#include "supp/expr_supp.h"
  
using namespace llvm;
using namespace std;

namespace euforia {
  inline std::string func_decl_string(const z3::expr& e) {
    const char *str = Z3_func_decl_to_string(e.ctx(), e.decl());
    std::string s(str);
    assert(s.data() != str);
    return s;
  }
  
  ostream& PrimaryInput::Print(ostream& os) const {
    os << "PrimaryInput<" << name << ":" << func_decl_string(z) << ">";
    return os;
  }
  
  PlainPrimaryInput::PlainPrimaryInput(std::string name, z3::expr z) 
      : PrimaryInput(name, z, kind::Plain) {
    assert(!IsUninterp(z));
  }
  
  TermPrimaryInput::TermPrimaryInput(std::string name, z3::expr z) 
      : PrimaryInput(name, z, kind::Term) {
    //assert(IsUninterp(z));
  }

std::unique_ptr<PrimaryInput> MakeInput(const z3::expr& zvar) {
  unique_ptr<PrimaryInput> ret;
  ret = std::make_unique<PlainPrimaryInput>(
      zvar.decl().name().str(), zvar);
  return ret;
}

}
