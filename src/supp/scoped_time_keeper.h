// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SCOPED_TIME_KEEPER_H_
#define EUFORIA_SCOPED_TIME_KEEPER_H_

#include <chrono>

namespace euforia {

using TimerClock = std::conditional<std::chrono::high_resolution_clock::is_steady,
      std::chrono::high_resolution_clock,
      std::chrono::steady_clock>::type;

//! TimerDuration d(0);
//! fmt::print("{:.3f} ms", d.count())
using TimerDuration = std::chrono::duration<double>;


//!
// {
// Duration running_duration(0);
// ScopedTimeKeeper keep(&running_duration);
// ... do something that takes time ...
// keep.Get(); // get the current duration
// } // deallocating timekeeper adds to running_duration
// 
// Code inspired by ic3ia.
// Duration needs operator+= and operator+
template <typename Duration = TimerDuration>
class ScopedTimeKeeper {
  Duration *out_;
  TimerClock clock_;
  std::chrono::time_point<TimerClock> start_;
  std::chrono::time_point<TimerClock> end_;

 public:
  inline ScopedTimeKeeper(Duration *duration_out) : out_(duration_out) {
    Reset();
  }

  inline void SetDurationOut(Duration *duration_out) {
    out_ = duration_out;
  }
  
  inline ~ScopedTimeKeeper() {
    *out_ += Get();
  }

  //! Reset start and end time
  inline void Reset() {
    start_ = clock_.now();
    end_ = start_;
  }

  //! Get the total time now
  inline Duration GetTotal() const {
    return *out_ + Get();
  }

  //! Get the time since last reset
  // XXX get rid of this
  inline TimerDuration Get() const {
    auto diff = clock_.now() - start_;
    return diff;
  }
  
  TimerDuration get() const {
    return Get();
  }
};

} // end namespace euforia

#endif
