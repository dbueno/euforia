// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_CUBE_INSERT_ITERATOR_H_
#define EUFORIA_CUBE_INSERT_ITERATOR_H_

#include "checker_types.h"
#include "cube.h"

#include <boost/optional/optional.hpp>
#include <boost/iterator/iterator_facade.hpp>

namespace euforia {
class TransitionSystem;
namespace detail {
struct XsysCube {
  XsysCube(const TransitionSystem& xsys, Cube& cube) : xsys(xsys), cube(cube) {}
  bool operator==(const XsysCube& other) const {
    return &xsys == &other.xsys && &cube == &other.cube;
  }
  const TransitionSystem& xsys;
  Cube& cube;
};

class CubeProxy {
 public:
  CubeProxy(XsysCube xc) : xc_(xc) {}
  void operator=(z3::expr e);

 private:
  XsysCube xc_;
};
} // end namespace detail

//! Can be used via TransitionSystem.cube_inserter or directly.
class CubeInsertIterator
    : public boost::iterator_facade<
          CubeInsertIterator, detail::CubeProxy, std::output_iterator_tag,
          detail::CubeProxy> {
 public:
  CubeInsertIterator() = default;
  CubeInsertIterator(const TransitionSystem& xsys, Cube& cube)
      : xc_(detail::XsysCube(xsys, cube)) {}

 private:
  boost::optional<detail::XsysCube> xc_;

  friend class boost::iterator_core_access;

  void increment() {}
  void decrement() {}
  bool equal(const CubeInsertIterator& other) const { return xc_ == other.xc_; }

  auto dereference() const {
    ENSURE(xc_);
    return detail::CubeProxy(*xc_);
  }

};

} // end namespace euforia

#endif
