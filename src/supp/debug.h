// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_DEBUG_H_
#define EUFORIA_DEBUG_H_

#include <iostream>

#define ENSURE(x) if (!(x)) { \
  std::cerr << "ENSURE violation: " << #x << "\n"; \
  exit(1); \
}




#ifdef NDEBUG
#define DEBUG_CODE(code) do {} while (0)
// this macro can be used where if the assert were compiled out, i would get
// warnings about unused vars
#define EUFORIA_ASSERT(b, ...) do {} while (0)
#else
#define DEBUG_CODE(code) do { code } while (0)

#define EUFORIA_ASSERT(b, ...) if (!(b)) { \
  fmt::print(std::cerr, __VA_ARGS__); \
  assert(b); \
}
#endif

#if defined(EXPENSIVECHECKS) && !defined(NDEBUG)
// XXX use EASSERT instead of EUFORIA_EXPENSIVE_ASSERT
#define EUFORIA_EXPENSIVE_ASSERT(b, ...) if (!(b)) { \
  fmt::print(std::cerr, __VA_ARGS__); \
  assert(b); \
}
#define EASSERT(b) assert(b)
#define EDEBUG_CODE(code) do { code } while (0)
#else
#define EUFORIA_EXPENSIVE_ASSERT(b, ...) do {} while (false)
#define EASSERT(b) do {} while (0)
#define EDEBUG_CODE(code) do {} while (0)
#endif

#define EUFORIA_DEBUG_BREAK __asm__("int $3")

#define _unused(x) ((void)(x))

#define EUFORIA_UNREACHABLE() abort()

namespace euforia {

void CreduceAssert(bool x);
class TransitionSystem;
void CreduceRegulateTransitionSystem(const TransitionSystem& xsys);

} // end namespace euforia

#endif
