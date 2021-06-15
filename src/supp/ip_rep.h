// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef ip_rep_hpp
#define ip_rep_hpp

#include "checker_types.h"
#include "one_hot.h"
#include "xsys/state_vars.h"

namespace euforia {

/// Representation of the IP. Currently we use a one-hot Boolean encoding.
class IpRepr {
 public:
  IpRepr(z3::context& c) : oh_current_(c), oh_next_(c) {}
  
  // treat the following as locations
  void init(const std::vector<StateVarRef>& locations);
  
  const OneHotConstraints& current() const { return oh_current_; }
  const OneHotConstraints& next() const { return oh_next_; }
  
  inline bool getID(const z3::expr& e, std::size_t& ID /* out */) const {
    if (auto loc = expr_to_id_.find(e); loc == expr_to_id_.end()) {
      return false;
    } else {
      ID = loc->second;
      return true;
    }
  }
  
  void print(std::ostream& os) const;
  
  
 private:
  /// Add STG node with ID
  //void addID(const stg_node& n);
  //friend class abstract_stg_transition_system;
  
  /// maps state vars to the node IDs they represent
  StateVarMap<std::size_t> bool_to_id_;
  /// inverse of bool_to_id_
  std::unordered_map<std::size_t, StateVarRef> id_to_bool_;
  ExprMap<std::size_t> expr_to_id_; // can be indexed by curr & next state
  // The one-hots do NOT contain the W-nodes. Every other location is there, though.
  OneHotConstraints oh_current_; // current
  OneHotConstraints oh_next_; // next
  
  
};
}
  
#endif
