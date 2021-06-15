// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef euforia__state_vars__
#define euforia__state_vars__

#include <functional>
#include <iosfwd>
#include <numeric>

#include "abstract_model.h"
#include "checker_types.h"
#include "supp/std_supp.h" // starts_with



namespace euforia {

/*-----------------------------------------------------------------------------------*/
/* STATE VARIABLES */

class StateVar {
 public:
  enum kind {
    kPlain, // normal scalar
    kArray, // a[t1] -> t2
    kTerm,  // uninterpreted
    TermArray // a[term] -> term
  };


  StateVar() = delete;
  StateVar(const StateVar&) = delete;
  void operator=(const StateVar& x) = delete;
  virtual ~StateVar() = default;

  inline const std::string& name() const { return name_; }
  inline const z3::expr& current() const { return zcurr_; }
  inline const z3::expr& next() const { return znext_; }

  inline bool operator==(const StateVar& other) const {
    return name_ == other.name_;
  }
  inline bool operator!=(const StateVar& other) const {
    return !(*this == other);
  }

  //! just hashes based on name
  inline std::size_t hash() const {
    return hash_;
  }

  inline z3::context& ctx() const { return zcurr_.ctx(); }

  virtual z3::expr zero() const { EUFORIA_FATAL("not supported"); }

  // Whether this variable is an uninterpreted term or array
  bool is_term() const;

  inline bool is_location() const {
    return false;
    // return name_[0] == '@'; // returns true for Wait vars as well
  }
  
  inline bool is_wait() const {
    return false;
    // return starts_with(name_, "@W");
  }
  
  inline bool is_location_not_wait() const {
    return false;
    // return name_[0] == '@' && name_.size() > 1 && name_[1] != 'W';
  }

  virtual std::ostream& Print(std::ostream& os) const;

  inline enum kind kind() const { return kind_; }

 protected:
  StateVar(std::string name, z3::expr zcurr, z3::expr znext, enum kind k)
      : name_(name), hash_(std::hash<std::string>()(name)), kind_(k),
      zcurr_(zcurr), znext_(znext) {
        assert(z3::eq(zcurr.get_sort(), znext.get_sort()));
      }

 private:
  const std::string name_;
  const z3::expr zcurr_;
  const z3::expr znext_;
  const enum kind kind_;
  const std::size_t hash_;

};

using StateVarRef = std::reference_wrapper<const StateVar>;

inline std::ostream& operator<<(std::ostream& os, const euforia::StateVar& c) {
  return c.Print(os);
}


/*-----------------------------------------------------------------------------------*/

// Bool, BitVec, that sort of thing
class PlainStateVar final : public StateVar {
  friend class StateVar;

 public:
  PlainStateVar(std::string name, z3::expr zcurr, z3::expr znext) 
      : StateVar(name, zcurr, znext, kind::kPlain) {}

  virtual std::ostream& Print(std::ostream& os) const override {
    os << "plain_var<" << current().decl() << "/" << next().decl() << ">";
    return os;
  }

  static bool classof(const StateVar* sv) {
    return sv->kind() == kPlain;
  }

};

/*-----------------------------------------------------------------------------------*/

class ArrayStateVar final : public StateVar {
  friend class StateVar;

 public:
  ArrayStateVar(std::string name, z3::expr zcurr, z3::expr znext);

  // in order to *explicitly* initialize arrays with stores, we distinguish
  // an uninit version of the array
  z3::expr getUninitVersion() const;


  virtual std::ostream& Print(std::ostream& os) const override {
    os << "array_var<" << current().decl() << "/" << next().decl() << ">";
    return os;
  }

  static bool classof(const StateVar* sv) { return sv->kind() == kArray; }

};

/*-----------------------------------------------------------------------------------*/

class TermStateVar final : public StateVar {
  friend class StateVar;

 public:
  TermStateVar(std::string name, z3::expr zcurr, z3::expr znext) 
      : StateVar(name, zcurr, znext, kind::kTerm) {}

  virtual std::ostream& Print(std::ostream& os) const override {
    os << "term_var<" << current().decl() << "/" << next().decl() << ">";
    return os;
  }

  static bool classof(const StateVar* sv) { return sv->kind() == kTerm; }
};


class TermArrayStateVar final : public StateVar {
  friend class StateVar;
 public:
  TermArrayStateVar(std::string name, z3::expr zcurr, z3::expr znext);

  virtual std::ostream& Print(std::ostream& os) const override {
    os << "term_array_var<" << current().decl() << "/" << next().decl() << ">";
    return os;
  }

  static bool classof(const StateVar* sv) {
    return sv->kind() == TermArray;
  }

};


std::unique_ptr<StateVar>
MakeStateVar(const z3::expr& zcurr, const z3::expr& znext);

struct HashStateVar {
  inline std::size_t operator()(const euforia::StateVarRef& k) const {
    return k.get().hash();
  }
};

struct EqualToStateVar {
  inline bool operator()(const euforia::StateVarRef& lhs,
                  const euforia::StateVarRef& rhs ) const {
    return lhs.get() == rhs.get();
  }
};

using StateVarSet = std::unordered_set<StateVarRef, HashStateVar,
      EqualToStateVar>;

template<typename T>
using StateVarMap = std::unordered_map<StateVarRef, T,
      HashStateVar, EqualToStateVar>;

}


#endif
