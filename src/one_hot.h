// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef one_hot_hpp
#define one_hot_hpp

#include <memory>

#include "checker_types.h"
#include "supp/expr_supp.h"

namespace euforia {
/// Knows how to efficiently express a one hot encoding for the (mutable) set of bools given.
class OneHotConstraints {
  ExprSet bools;

 public:

  struct Config {
    enum { kNaive, kCommander } encoding_type;
    int commander_max_size;
    /// Configures for naive encoding
    Config() : encoding_type(kNaive) {}
    /// Configures for commander encoding with given max size
    Config(int max_size) 
        : encoding_type(kCommander), commander_max_size(max_size) {}

    static Config Naive() {
      return Config();
    }
    static Config Commander(const int max_size) {
      return Config(max_size);
    }
  };

  OneHotConstraints(z3::context& c);
  OneHotConstraints(const OneHotConstraints&);
  OneHotConstraints& operator=(const OneHotConstraints&) = delete;
  OneHotConstraints(OneHotConstraints&&) = delete;
  OneHotConstraints& operator=(OneHotConstraints&&);
  ~OneHotConstraints();

  const ExprSet& getBools() const { return bools; }

  const ExprSet& commander_vars() const;

  template <typename Iter>
  void insert(Iter it, Iter ie) {
    while (it != ie) {
      addBool(*it++);
    }
  }

  void Insert(const z3::expr& e) {
    return addBool(e);
  }
  
  /// Add a Boolean state var to this one-hot set
  void addBool(const z3::expr& e) {
    assert(e.is_bool());
    bools.emplace(std::cref(e));
  }

  /// Get one-hot constraints to assert
  z3::expr at_most(const Config& c);

  /// Get the list of constraints that force the Bools to be exactly one-hot
  std::vector<z3::expr> constraintsExactly() const;

  /// Get the list of constraints that force the Bools to be at-most-one hot
  std::vector<z3::expr> constraintsAtMost() const;

  z3::context& ctx() const { z3::expr b = *bools.begin(); return b.ctx(); }

 private:
  class Impl;
  std::unique_ptr<Impl> pimpl_;
};
}

#endif /* one_hot_hpp */
