// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/ip_rep.h"
#include "xsys/transition_system.h"

#include <llvm/Support/Casting.h>

#include <string>

using namespace std;
using namespace llvm;

namespace euforia {
void IpRepr::init(const vector<StateVarRef>& locations) {
  for (const StateVar& location_var : locations) {
    assert(location_var.is_location());
    string ID_string(location_var.name().begin() + 2, location_var.name().end()); // skip @L, this is a HACK
    size_t nchars_found = 0;
    auto ID = stoi(ID_string, &nchars_found);
    assert(nchars_found > 0);
    expr_to_id_.emplace(location_var.current(), ID);
    expr_to_id_.emplace(location_var.next(), ID);
    bool_to_id_.emplace(location_var, ID);
    id_to_bool_.emplace(ID, location_var);
    oh_current_.addBool(location_var.current());
    oh_next_.addBool(location_var.next());
  }
}
  
void IpRepr::print(std::ostream& os) const {
  os << "locations (" << bool_to_id_.size() << "):" << endl;
  for (auto& p : bool_to_id_) {
    os << "  " << p.first << endl;
  }
}

}


