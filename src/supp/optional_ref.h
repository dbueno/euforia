// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_OPTIONAL_REF_H_
#define EUFORIA_SUPP_OPTIONAL_REF_H_

#include <boost/optional.hpp>
#include <functional>

// This type is here because I first tried to use llvm::Optional<StateVarRef>
// but then clients needed to explicitly call get() to remove the reference
// wrapper so here we are.
template <typename T>
class OptionalRef {
  using Ref = std::reference_wrapper<T>;
 public:
  OptionalRef(const T& v) : v_(v) {}
  OptionalRef(const boost::none_t&) {}
  OptionalRef() {}

  inline operator bool() const {
    return bool(v_);
  }

  inline operator boost::optional<Ref>() const {
    return v_;
  }

  inline const T& operator*() const {
    return v_->get();
  }

  inline const T *operator->() const {
    return &v_->get();
  }

  inline OptionalRef& operator=(const T& v) {
    v_ = v;
    return *this;
  }

 private:
  boost::optional<Ref> v_;
};

#endif
