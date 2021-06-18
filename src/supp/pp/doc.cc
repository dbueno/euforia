// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/pp/doc.h"

#include <llvm/Support/CommandLine.h>
#include <map>
#include <memory>

#include "supp/logger.h"

using namespace std;

//^----------------------------------------------------------------------------^
// Configuration

namespace euforia {
namespace pp {

int best_width;

namespace {
using namespace llvm;
cl::opt<int, true> pp_best_width(
    "pp-width",
    cl::desc("Max width for pretty printing"),
    cl::location(best_width),
    cl::init(160));
} // namespace
} // namespace pp
} // namespace euforia

//^----------------------------------------------------------------------------^

namespace {
using namespace euforia::pp;

enum class Mode { kFlat, kBreak };
using Elt = std::tuple<int, Mode, DocPtr>;
}

template <>
struct fmt::formatter<Mode> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    ENSURE(it == end);
    return it;
  }

  template <typename FormatContext>
  auto format(const Mode& m, FormatContext& ctx) -> decltype(ctx.out()) {
    switch (m) {
      case Mode::kFlat:
        return format_to(ctx.out(), "kFlat");
      case Mode::kBreak:
        return format_to(ctx.out(), "kBreak");
      default:
        EUFORIA_UNREACHABLE();
    }
  }
};


namespace euforia {
namespace pp {

using namespace details;

DocPtr empty() {
  return std::make_shared<Empty>();
}

DocPtr append(DocPtr lhs, DocPtr rhs) {
  ENSURE(lhs);
  ENSURE(rhs);
  if (std::dynamic_pointer_cast<Empty>(lhs) &&
      std::dynamic_pointer_cast<Empty>(rhs)) {
    return empty();
  } else if (std::dynamic_pointer_cast<Empty>(lhs)) {
    return rhs;
  } else if (std::dynamic_pointer_cast<Empty>(rhs)) {
    return lhs;
  }
  return std::make_shared<Append>(lhs, rhs);
}
  
DocPtr append(std::initializer_list<DocPtr> elts) {
  auto it = elts.begin(), ie = elts.end();
  if (it == ie)
    return empty();
  DocPtr r = *it++;
  while (it != ie) {
    r = append(r, *it++);
  }
  return r;
}

DocPtr nest(int indent, DocPtr d) {
  ENSURE(d);
  return std::make_shared<Nest>(indent, d);
}

DocPtr text(std::string&& s) {
  return std::make_shared<Text>(std::forward<std::string>(s));
}

DocPtr decimal(int i) {
  return text(to_string(i));
}

DocPtr text(const std::string& s) {
  return std::make_shared<Text>(s);
}

DocPtr break_(int sp, int off) {
  return std::make_shared<Break>(sp, off);
}

DocPtr sp(int off) {
  return break_(1, off);
}

DocPtr line() {
  return break_(1, 0);
}

DocPtr newline() {
  return std::make_shared<Newline>();
}

DocPtr group(DocPtr g) {
  ENSURE(g);
  return std::make_shared<Group>(g);
}

DocPtr paren(DocPtr d) {
  ENSURE(d);
  return append(text("("), d, text(")"));
}

DocPtr PpAst(DocPtr p) {
  map<DocPtr, DocPtr> rw;
  vector<DocPtr> q{{{p}}};
  auto all_rw1 = [&](const DocPtr a) {
    return rw.find(a) != rw.end(); };
  auto all_rw2 = [&](const DocPtr a, const DocPtr b) {
    return all_rw1(a) && all_rw1(b); };
  // q - queue of unprocessed elements
  // r - what top of q rewrites to
  while (!q.empty()) {
    auto x = q.back();
    logger.Log(0, "x:{} q.size:{}", JustType(x), q.size());
    switch (x->getKind()) {
      case DocKind::kEmpty:
        q.pop_back();
        rw.insert({x, text("#")});
        break;

      case DocKind::kText: {
        q.pop_back();
        auto t = dynamic_pointer_cast<Text>(x);
        rw.insert({x, group(append(
                        text("\""), text(t->str), text("\"")))});
        break;
      }

      case DocKind::kNewline: {
        q.pop_back();
        rw.insert({x, text("nl")});
        break;
      }
        
      case DocKind::kBreak: {
        q.pop_back();
        auto b = dynamic_pointer_cast<Break>(x);
        rw.insert({x,
                  text(fmt::format("break({},{})", b->sp, b->off))});
        break;
      }

      case DocKind::kNest: {
        auto n = dynamic_pointer_cast<Nest>(x);
        if (!all_rw1(n->doc)) {
          q.push_back(n->doc);
        } else {
          q.pop_back();
          auto d = rw.at(n->doc);
          rw.insert({n, group(append(
                          text("nest"),
                          text(to_string(n->indent)),
                          text("("),
                          break_(0, 2),
                          nest(2, d),
                          text(")")))});

        }
        break;
      }

      case DocKind::kAppend: {
        auto app = dynamic_pointer_cast<Append>(x);
        if (!all_rw2(app->lhs, app->rhs)) {
          q.push_back(app->rhs);
          q.push_back(app->lhs);
        } else {
          q.pop_back();
          auto lhs = rw.at(app->lhs);
          auto rhs = rw.at(app->rhs);
          rw.insert({app, group(append(
                          text("["), lhs, break_(1, 0), rhs, text("]")))});
        }
        break;
      }

      case DocKind::kGroup: {
        auto grp = dynamic_pointer_cast<Group>(x);
        if (!all_rw1(grp->g)) {
          q.push_back(grp->g);
        } else {
          q.pop_back();
          auto g = rw.at(grp->g);
          rw.insert({grp, group(append(
                          text("group("),
                          break_(0, 2), nest(2, g), break_(0, 0),
                          text(")")))});
        }
        break;
      }
    }
  }
  return rw.at(p);
}

}
}

namespace {
using namespace euforia::pp;
using namespace euforia::pp::details;

template <typename T>
std::vector<T> push_back_pure(T&& e, const std::vector<T>& v) {
  vector<T> v2{v};
  v2.emplace_back(std::forward<T>(e));
  return v2;
}

bool fitting(vector<Elt>&& elts, int left0) {
  vector<Elt> q{std::forward<vector<Elt>>(elts)};
  int left = left0;
  while (!q.empty()) {
    auto& [i, mode, doc] = q.back();
    // fmt::print("fitting: i:{} left:{} mode:{} top:{}\n", i, left, mode, JustType(doc));
    q.pop_back();
    if (left >= 0) {
      switch (doc->getKind()) {
        case DocKind::kEmpty:
          break;

        case DocKind::kAppend: {
          auto app = dynamic_pointer_cast<Append>(doc);
          q.push_back({i, mode, app->rhs});
          q.push_back({i, mode, app->lhs});
          break;
        }

        case DocKind::kNest: {
          auto n = dynamic_pointer_cast<Nest>(doc);
          q.push_back({i + n->indent, mode, n->doc});
          break;
        }

        case DocKind::kText: {
          auto t = dynamic_pointer_cast<Text>(doc);
          left -= t->str.size();
          break;
        }

        case DocKind::kBreak: {
          auto b = dynamic_pointer_cast<Break>(doc);
          switch (mode) {
            case Mode::kFlat:
              left -= b->sp;
              break;

            case Mode::kBreak:
              return true;
          }
          break;
        }

        case DocKind::kNewline:
          return true;

        case DocKind::kGroup: {
          auto g = dynamic_pointer_cast<Group>(doc);
          q.push_back({i, mode, g->g});
          break;
        }
      }
    } else {
      // No more left; doesn't fit.
      return false;
    }
  }
  return true;
}

}


namespace euforia {
namespace pp {
// w - linewidth
// k - number of chars already used on current line
// i - indent after linebreaks
void Pp::best(const int w, const DocPtr& x) {
  int k{};
  vector<Elt> q{{{0, Mode::kBreak, x}}};
  while (!q.empty()) {
    auto& [i, mode, doc] = q.back();
    q.pop_back();
    logger.Log(7, "best: i:{} k:{} mode:{} doc:{} size:{}", i, k, mode, JustType(doc), q.size());
    if (i >= 200 || k >= 200) {
      // EUFORIA_DEBUG_BREAK;
    }
    switch (doc->getKind()) {
      case DocKind::kEmpty:
        break;

      case DocKind::kAppend: {
        auto app = dynamic_pointer_cast<Append>(doc);
        // Visit rhs second.
        q.push_back({i, mode, app->rhs});
        //             // Visit lhs first.
        q.push_back({i, mode, app->lhs});
        break;
      }

      case DocKind::kNest: {
        auto n = dynamic_pointer_cast<Nest>(doc);
        q.push_back({i + n->indent, mode, n->doc});
        break;
      }

      case DocKind::kText: {
        auto t = dynamic_pointer_cast<Text>(doc);
        output(t->str);
        k += t->str.size();
        break;
      }

      case DocKind::kBreak: {
        auto b = dynamic_pointer_cast<Break>(doc);
        auto sp = b->sp;
        auto off = b->off;
        switch (mode) {
          case Mode::kFlat:
            spaces(sp);
            k += sp;
            break;

          case Mode::kBreak:
            nlspace(i + off);
            k = i + off;
            break;
        }
        break;
      }

      case DocKind::kNewline:
        nlspace(i);
        k = i;
        break;

      case DocKind::kGroup: {
        auto g = dynamic_pointer_cast<Group>(doc);
        auto xp = g->g;
        bool f;
        switch (mode) {
          case Mode::kFlat:
            q.push_back({i, Mode::kFlat, xp});
            break;

          case Mode::kBreak:
            f = fitting(push_back_pure({i, Mode::kFlat, xp}, q), w - k);
            logger.Log(7, "best fitting?:{}", f);
            if (f) {
              q.push_back({i, Mode::kFlat, xp});
            } else {
              q.push_back({i, Mode::kBreak, xp});
            }
            break;
        }
        break;
      }
    }

  }
}

void Best(Pp& s, const DocPtr& d) {
  s.best(best_width, d);
}


} // namespace pp
} // namespace euforia
