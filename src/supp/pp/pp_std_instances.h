#ifndef EUFORIA_SUPP_PP_PP_STD_INSTANCES_H_
#define EUFORIA_SUPP_PP_PP_STD_INSTANCES_H_

#include <unordered_set>
#include <unordered_map>
#include <set>
#include <vector>

#include "supp/debug.h"
#include "supp/pp/doc.h"

template <typename T, typename Allocator>
struct euforia::pp::PrettyPrinter<std::vector<T, Allocator>> {
  euforia::pp::DocPtr operator()(const std::vector<T, Allocator>& v) {
    auto g = pp::commabox(v.begin(), v.end(), pp::text(","));
    pp::DocStream d;
    return d << "vector<" << pp::nest(4, g) << ">";
  }
};

template <typename T, class Hash, class Pred, class Allocator>
struct euforia::pp::PrettyPrinter<std::unordered_set<T, Hash, Pred, Allocator>> {
  euforia::pp::DocPtr operator()(const std::unordered_set<T, Hash, Pred, Allocator>& s) {
    auto g = pp::commabox(s.begin(), s.end(), pp::text(","));
    pp::DocStream d;
    return d << "uset{" << pp::nest(4, g) << "}";
  }
};

#endif
