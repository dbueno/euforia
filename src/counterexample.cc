// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "counterexample.h"
#include "tslice.h"


using namespace std;
using namespace llvm;

namespace euforia {


/*-----------------------------------------------------------------------------------*/ 

using namespace boolector;
BoolectorCounterexample::BoolectorCounterexample(shared_ptr<boolector::BtorWrapper> B) : B(B) {}

size_t BoolectorCounterexample::length() const {
  assert(cstates.size() == cinputs.size()+1);
  return cstates.size()-1;
}

static void printVarAssignment(std::ostream& os, const cx_var_assignment& a) {
  for (auto& p : a) {
    auto& v = p.first;
    os << v << ": " << *p.second << endl;
  }
}

static void printVarAssignment(std::ostream& os, int stateNum, const cx_var_assignment& prev, const cx_var_assignment& inputs, const cx_var_assignment& curr) {
  for (auto& [name, assign] : inputs) {
    os << name << " <- " << *assign << endl;
  }
  
  os << endl << "state " << stateNum << endl;
  for (auto& [v, assign] : curr) {
    auto& preva = prev.at(v);
    if (*preva != *assign) {
      os << v << ": " << *assign << endl;
    }
  }
}

void BoolectorCounterexample::print(std::ostream& os) const {
  assert(cstates.size() > 0);
  os << "boolector Counterexample:" << endl;
  os << "initial state (state 0)" << endl;
  printVarAssignment(os, cstates.at(0));
  for (size_t i = 1; i < cstates.size(); i++) {
    os << endl;
    printVarAssignment(os, i, cstates.at(i-1), cinputs.at(i-1), cstates.at(i));
  }
}

//^----------------------------------------------------------------------------^
//


void SCounterexample::print(std::ostream& os) const {
  // We want to just print the assignments and stuff from the states
  fmt::print(os, "{}-step counterexample:\n", length());
  for (size_t i = 0 ; i < states_.size(); i++) {
    const auto& s = states_[i];
    fmt::print(os, "state {}:\n", i);
    fmt::print(os, "{}\n", *s->pre_step_model());
  }
}
  
}
