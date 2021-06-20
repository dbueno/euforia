#ifndef EUFORIA_FMT_SUPP_H_
#define EUFORIA_FMT_SUPP_H_

#include <fmt/format.h>
#include <unordered_set>
#include <unordered_map>
#include <set>
#include <vector>

#include "supp/debug.h"
#include "supp/pp/doc.h"

template <typename T>
struct fmt::formatter<std::vector<T>> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    ENSURE(it == end);
    return it;
  }

  template <typename FormatContext>
  auto format(const std::vector<T>& v, FormatContext& ctx) -> decltype(ctx.out()) {
    auto out = ctx.out();
    out = format_to(out, "vector<{}>", fmt::join(v, ", "));
    return out;
  }
};

template <typename T, class Hash, class Pred, class Allocator>
struct fmt::formatter<std::unordered_set<T, Hash, Pred, Allocator>> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    ENSURE(it == end);
    return it;
  }

  template <typename FormatContext>
  auto format(const std::unordered_set<T, Hash, Pred, Allocator>& v, FormatContext& ctx) -> decltype(ctx.out()) {
    auto out = ctx.out();
    out = format_to(out, "uset<{}>", fmt::join(v, ", "));
    return out;
  }
};

template <typename Key, class Compare, class Allocator>
struct fmt::formatter<std::set<Key, Compare, Allocator>> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    ENSURE(it == end);
    return it;
  }

  template <typename FormatContext>
  auto format(const std::set<Key, Compare, Allocator>& v, FormatContext& ctx) -> decltype(ctx.out()) {
    auto out = ctx.out();
    out = format_to(out, "set<{}>", fmt::join(v, ", "));
    return out;
  }
};


template <class Key, class T, class Hash, class KeyEqual, class Allocator>
struct fmt::formatter<std::unordered_map<Key, T, Hash, KeyEqual, Allocator>> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    ENSURE(it == end);
    return it;
  }

  template <typename FormatContext>
  auto format(const std::unordered_map<Key, T, Hash, KeyEqual, Allocator>& v, FormatContext& ctx) -> decltype(ctx.out()) {
    auto out = ctx.out();
    out = format_to(out, "umap:\n");
    for (auto&& p : v) {
      out = format_to(out, "  {} -> {}\n", p.first, p.second);
    }
    return out;
  }
};


template <typename T>
struct fmt::formatter<std::unique_ptr<T>> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    ENSURE(it == end);
    return it;
  }

  template <typename FormatContext>
  auto format(const std::unique_ptr<T>& v, FormatContext& ctx) -> decltype(ctx.out()) {
    auto out = ctx.out();
    if (v) {
      out = format_to(out, "uptr<{}>", *v);
    } else {
      out = format_to(out, "uptr<null>");
    }
    return out;
  }
};

template <typename T>
struct fmt::formatter<std::shared_ptr<T>> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    ENSURE(it == end);
    return it;
  }

  template <typename FormatContext>
  auto format(const std::shared_ptr<T>& v, FormatContext& ctx) -> decltype(ctx.out()) {
    auto out = ctx.out();
    if (v) {
      out = format_to(out, "sptr<{}>", *v);
    } else {
      out = format_to(out, "sptr<null>");
    }
    return out;
  }
};

template <typename T>
struct euforia::pp::PrettyPrinter<std::shared_ptr<T>> {
  DocPtr operator()(const std::shared_ptr<T>& p) const {
    euforia::pp::DocStream s;
    s << "sptr<" << (p ? Pprint(*p) : euforia::pp::text("null")) << ">";
    return s;
  }
};

#endif
