// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_STATISTICS_H_
#define EUFORIA_STATISTICS_H_

#include <boost/variant.hpp>
#include <iostream>
#include <vector>

namespace euforia {

class Statistics {

 public:
  using Val = boost::variant<int64_t, double>;

  void Reset();
  void Update(const char *key, int64_t inc);
  void Update(const char *key, double inc);
  size_t size() const;
  const char *get_key(size_t idx) const;
  void Print(std::ostream& out) const;

  static Val add_val(const Val& v1, const Val& v2);

 private:
  using KeyValPair = std::pair<const char *, Val>;
  std::vector<KeyValPair> stats_;
};

// put in euforia namespace for ADL
inline std::ostream& operator<<(std::ostream& os,
                                const Statistics& st) {
  st.Print(os);
  return os;
}

} // end namespace euforia

#endif // EUFORIA_STATISTICS_H_
