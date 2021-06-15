// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/statistics.h"

#include <fmt/format.h>
#include <fmt/ostream.h>
#include <map>

#include "supp/debug.h"

using namespace std;

namespace euforia {

void Statistics::Reset() {
  stats_.clear();
}

void Statistics::Update(const char *key, int64_t inc) {
  if (inc != 0) {
    stats_.push_back(KeyValPair(key, inc));
  }
}

void Statistics::Update(const char *key, double inc) {
  if (inc != 0.0) {
    stats_.push_back(KeyValPair(key, inc));
  }
}

size_t Statistics::size() const {
  return stats_.size();
}

const char *Statistics::get_key(size_t idx) const {
  return stats_.at(idx).first;
}

using StatMap = map<const char *, Statistics::Val>;

Statistics::Val Statistics::add_val(const Statistics::Val& v1,
                                    const Statistics::Val& v2) {
  assert(v1.which() == v2.which());
  switch (v1.which()) {
    case 0:
      return boost::get<int64_t>(v1) + boost::get<int64_t>(v2);

    case 1:
      return boost::get<double>(v1) + boost::get<double>(v2);
  }
  EUFORIA_UNREACHABLE();
}

template<typename V, typename M>
static void make_map(const V& v, M& m) {
  typename V::const_iterator it  = v.begin();
  typename V::const_iterator end = v.end();
  for (; it != end; ++it) {
    if (auto elt = m.find(it->first); elt != m.end()) {
      m.erase(it->first);
      m.insert({it->first, Statistics::add_val(it->second, elt->second)});
    } else { m.insert({it->first, it->second}); }
  }
}


void Statistics::Print(std::ostream& os) const {
  StatMap m;
  make_map(stats_, m);
  class F {
   public:
    F(std::ostream& os) : os_(os) {}
    void operator()(int64_t v) { fmt::print(os_, "{}", v); }
    void operator()(double v) { fmt::print(os_, "{:.5f}", v); };
   private:
    std::ostream& os_;
  };

  for (const auto& [k, v] : m) {
    fmt::print(os, "{}: ", k);
    boost::apply_visitor(F(os), v);
    fmt::print(os, "\n");
  }
}

} // end namespace euforia
