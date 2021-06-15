// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef euforia__primary_inputs__
#define euforia__primary_inputs__

#include <functional>
#include <numeric>
#include <string>
#include <unordered_map>

#include "checker_types.h"
#include "supp/expr_supp.h"



namespace euforia {

class reachability_graph;
class AbstractModel;
class uninterpreted_partition;
class TrackingSolver;
class CheckerSat;

/*-----------------------------------------------------------------------------------*/
/* PRIMARY INPUTS */

class PrimaryInput {
 public:
  enum kind {
    Plain, // normal scalar
    Term   // uninterpreted
  };

  const std::string name;
  const z3::expr z;
  const enum kind kind;

  virtual ~PrimaryInput() = default;
  PrimaryInput(const PrimaryInput&) = delete;
  void operator=(const PrimaryInput& x) = delete;

  operator z3::expr() const { return z; }

  operator z3::ExprWrapper() const { return z; }

  bool operator==(const PrimaryInput& other) const {
    return name == other.name;
  }

  inline std::size_t hash() const {
    return hash_;
  }

  enum kind getKind() const { return kind; }

  virtual std::ostream& Print(std::ostream& os) const;

 protected:
  PrimaryInput(std::string name, z3::expr z, enum kind kind) 
      : name(name), z(z), kind(kind), hash_(std::hash<std::string>()(name)) {}

 private:
  const std::size_t hash_;
};

using PrimaryInputRef = std::reference_wrapper<const PrimaryInput>;
inline std::ostream& operator<<(std::ostream& os, const PrimaryInput& c) {
  return c.Print(os);
}


class PlainPrimaryInput final : public PrimaryInput {
 public:
  PlainPrimaryInput(std::string name, z3::expr z);

  static bool classof(const PrimaryInput* i) { return i->getKind() == Plain; }

};


/*-----------------------------------------------------------------------------------*/

class TermPrimaryInput final : public PrimaryInput {
 public:
  TermPrimaryInput(std::string name, z3::expr z);

  static bool classof(const PrimaryInput* i) {
    return i->getKind() == Term;
  }

};

std::unique_ptr<PrimaryInput> MakeInput(const z3::expr& zcurr);


namespace {
struct HashPrimaryInput {
  std::size_t operator()(const euforia::PrimaryInput& k) const {
    return k.hash();
  }
};

struct EqualToPrimaryInput {
  bool operator()( const euforia::PrimaryInputRef& lhs,
                  const euforia::PrimaryInputRef& rhs ) const {
    return lhs.get() == rhs.get();
  }
};
}

template<typename T>
using primary_input_ueeeemap = std::unordered_map<PrimaryInputRef, T,
      HashPrimaryInput, EqualToPrimaryInput>;
  
}

#endif
