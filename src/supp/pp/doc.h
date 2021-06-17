// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno
//
#ifndef EUFORIA_SUPP_PP_DOC_H_
#define EUFORIA_SUPP_PP_DOC_H_

#include <fmt/format.h>
#include <llvm/Support/Casting.h>
#include <sstream>
#include <type_traits>

#include "supp/debug.h"


namespace euforia {
namespace pp {

struct Doc;
using DocPtr = std::shared_ptr<Doc>;

//! Users may provide PrettyPrinter instances for theis custom datatypes.
template <typename T, typename Enable = void>
struct PrettyPrinter {
  DocPtr operator()(const T&) = delete; // error if used
};

template <typename T>
DocPtr Pprint(const T& x) { return PrettyPrinter<std::decay_t<T>>()(x); }

enum class DocKind {
  kEmpty,
  kAppend,
  kNest,
  kText,
  kBreak,
  kNewline,
  kGroup
};

struct Doc {
  const DocKind kind;
  DocKind getKind() const { return kind; }

  Doc(DocKind k) : kind(k) {}
  virtual ~Doc() = default;
};

DocPtr empty();
DocPtr text(std::string&& s);
DocPtr text(const std::string& s);
DocPtr decimal(int i);
// Associative.
DocPtr append(DocPtr lhs, DocPtr rhs);
DocPtr append(std::initializer_list<DocPtr> elts);
inline DocPtr append(DocPtr a, DocPtr b, DocPtr c) { return append(append(a, b), c); }
inline DocPtr append(DocPtr a, DocPtr b, DocPtr c, DocPtr d) { return append(append(a, b, c), d); }
inline DocPtr append(DocPtr a, DocPtr b, DocPtr c, DocPtr d, DocPtr e) { return append(append(a, b, c, d), e); }
inline DocPtr append(DocPtr a, DocPtr b, DocPtr c, DocPtr d, DocPtr e, DocPtr f) { return append(append(a, b, c, d, e), f); }
inline DocPtr append(DocPtr a, DocPtr b, DocPtr c, DocPtr d, DocPtr e, DocPtr f, DocPtr g) { return append(append(a, b, c, d, e, f), g); }
inline DocPtr append(DocPtr a, DocPtr b, DocPtr c, DocPtr d, DocPtr e, DocPtr f, DocPtr g, DocPtr h) { return append(append(a, b, c, d, e, f, g), h); }
//! Indent document d.
DocPtr nest(int indent, DocPtr d);
//! Inserts n spaces or a linebreak; if break, then indent by offset on the
//! next line.
DocPtr break_(int sp, int off);
//! Same as break_(1, off).
DocPtr sp(int off);
//! Same as break_(1, 0).
DocPtr line();
DocPtr newline();
DocPtr group(DocPtr g);
DocPtr paren(DocPtr);

template <typename Iter>
DocPtr groupsep(Iter i, Iter end, DocPtr sep) {
  DocPtr ret = empty();
  bool first = true;
  for (;i != end; ++i) {
    if (first) {
      first = false;
      ret = Pprint(*i);
    } else {
      auto d = Pprint(*i);
      ret = group(append(ret, sep, d));
    }
  }
  return ret;
}

//! Puts sep between all elements and fits as many elements on one line before
//! going to the next line.
//!
//! Usage: sepbox(it, ie, text("&& ")) separates elements with && and breaks
//! lines just before separator if need be.
template <typename Iter>
DocPtr sepbox(Iter it, Iter ie, DocPtr sep) {
  return groupsep(it, ie, group(append(break_(1, 0), sep)));
}

//! Like sepbox, but breaks after the separator (like you would with a comma)
//! rather than before.
template <typename Iter>
DocPtr commabox(Iter it, Iter ie, DocPtr comma) {
  return groupsep(it, ie, group(append(comma, break_(1, 0))));
}

//! This class makes it easy to append, basically.
class DocStream {
 public:
  DocStream() {
    docs_.push_back(empty());
  }

  void print(std::string&& s) {
    append(pp::text(std::forward<std::string>(s)));
  }

  void append(DocPtr d) { docs_.back() = pp::append(docs_.back(), d); }

  DocPtr doc() const { return docs_.back(); }
  operator DocPtr() const { return docs_.back(); }

  DocStream& operator<<(DocPtr d) { append(d); return *this; }
  DocStream& operator<<(std::string&& s) { print(std::forward<std::string>(s)); return *this; }

 private:
  std::vector<DocPtr> docs_;
};

//! A prettyprinter outputs formatted text from a Doc.
class Pp {
 public:
  virtual ~Pp() = default;

  virtual void output(const std::string&) = 0;

  void spaces(int i) {
    ENSURE(i >= 0);
    for (int j = 0; j < i; j++) {
      output(" ");
    }
  }

  void nlspace(int i) {
    ENSURE(i >= 0);
    output("\n");
    for (int j = 0; j < i; j++) {
      output(" ");
    }
  }

  //! Outputs the document using [w] as max width.
  void best(const int w, const DocPtr& d);
};


extern int best_width;

//! Formats the doc using the given stream and the global pretty-printing
//! [best_width].
void Best(Pp& s, const DocPtr& d);

template <typename Stream>
class PpStream : public Pp {
 public:
  PpStream(Stream& s) : out(s) {}

  virtual void output(const std::string& s) override {
    out << s;
  }

 private:
  Stream& out;
};

template <typename FormatContext>
class PpFormatContext : public Pp {
 public:
  PpFormatContext(FormatContext& ctx) : ctx_(ctx) {}

  FormatContext& ctx() const { return ctx_; }

  virtual void output(const std::string& s) override {
    fmt::format_to(ctx_.out(), "{}", s);
  }

 private:
  FormatContext& ctx_;
};


namespace details {

struct Empty : public Doc {
  Empty() : Doc(DocKind::kEmpty) {}
  static bool classof(const Doc* d) { return d->getKind() == DocKind::kEmpty; }
};

struct Append : public Doc {
  Append(DocPtr l, DocPtr r) : lhs(l), rhs(r), Doc(DocKind::kAppend) {}
  static bool classof(const Doc* d) { return d->getKind() == DocKind::kAppend; }
  DocPtr lhs;
  DocPtr rhs;
};

struct Nest : public Doc {
  Nest(int i, DocPtr d) : indent(i), doc(d), Doc(DocKind::kNest) {}
  static bool classof(const Doc* d) { return d->getKind() == DocKind::kNest; }
  int indent;
  DocPtr doc;
};

struct Text : public Doc {
  Text(std::string&& s) : str(s), Doc(DocKind::kText) {}
  Text(const std::string& s) : str(s), Doc(DocKind::kText) {}
  static bool classof(const Doc* d) { return d->getKind() == DocKind::kText; }
  std::string str;
};

struct Break : public Doc {
  Break(int a, int b) : sp(a), off(b), Doc(DocKind::kBreak) {}
  static bool classof(const Doc* d) { return d->getKind() == DocKind::kBreak; }
  int sp;
  int off;
};

struct Newline : public Doc {
  Newline() : Doc(DocKind::kNewline) {}
  static bool classof(const Doc* d) { return d->getKind() == DocKind::kNewline; }
};

struct Group : public Doc {
  Group(DocPtr d) : g(d), Doc(DocKind::kGroup) {}
  static bool classof(const Doc* d) { return d->getKind() == DocKind::kGroup; }
  DocPtr g;
};


struct JustType {
  JustType(DocPtr d) : d(d) {}
  DocPtr d;
};
}


DocPtr PpAst(DocPtr p);


//^----------------------------------------------------------------------------^
// Default instances.

template <>
struct PrettyPrinter<std::string> {
  DocPtr operator()(const std::string& s) { return text(s); }
};

template <typename Arith>
struct PrettyPrinter<Arith,
    std::enable_if_t<std::is_arithmetic<Arith>::value>> {
  DocPtr operator()(const Arith k) { return text(std::to_string(k)); }
};

template <>
struct PrettyPrinter<DocPtr> {
  DocPtr operator()(const DocPtr& d) { return d; }
};

}
}

//^----------------------------------------------------------------------------^
// Formatters.

template <>
struct fmt::formatter<euforia::pp::details::JustType> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), end = ctx.end();
    ENSURE(it == end);
    return it;
  }

  template <typename FormatContext>
  auto format(const euforia::pp::details::JustType& t, FormatContext& ctx) -> decltype(ctx.out()) {
    using namespace euforia::pp;
    using namespace euforia::pp::details;
    const std::shared_ptr<Doc> doc = t.d;
    if (std::dynamic_pointer_cast<Empty>(doc)) {
      return format_to(ctx.out(), "Empty");
    } else if ( std::dynamic_pointer_cast<Append>(doc)) {
      return format_to(ctx.out(), "Append");
    } else if ( std::dynamic_pointer_cast<Nest>(doc)) {
      return format_to(ctx.out(), "Nest");
    } else if ( std::dynamic_pointer_cast<Text>(doc)) {
      return format_to(ctx.out(), "Text");
    } else if ( std::dynamic_pointer_cast<Break>(doc)) {
      return format_to(ctx.out(), "Break");
    } else if (std::dynamic_pointer_cast<Newline>(doc)) {
      return format_to(ctx.out(), "Newline");
    } else if ( std::dynamic_pointer_cast<Group>(doc)) {
      return format_to(ctx.out(), "Group");
    }
    EUFORIA_UNREACHABLE();
  }
};

//! Default Doc formatter formats the doc at width best_width.
template <>
struct fmt::formatter<euforia::pp::DocPtr> {
  int width = euforia::pp::best_width;

  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), ie = ctx.end();
    ENSURE(it == ie || *it == '}');
    return it;
  }

  template <typename FormatContext>
  auto format(const euforia::pp::DocPtr& doc, FormatContext& ctx) -> decltype(ctx.out()) {
    euforia::pp::PpFormatContext pp(ctx);
    pp.best(width, doc);
    return pp.ctx().out();
  }
};

//! Default DocStream formatter falls back on DocPtr.
template <>
struct fmt::formatter<euforia::pp::DocStream> {
  int width = euforia::pp::best_width;

  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), ie = ctx.end();
    ENSURE(it == ie || *it == '}');
    return it;
  }

  template <typename FormatContext>
  auto format(const euforia::pp::DocStream& doc, FormatContext& ctx) -> decltype(ctx.out()) {
    return format_to(ctx.out(), "{}", static_cast<euforia::pp::DocPtr>(doc));
  }
};

//! Use this to generate an instance of formatter that simply pretty prints the
//! object. fmt::formatter has extensive defaulting logic that I don't
//! understand, so I'm just providing this macro for now.
#define EUFORIA_FWD_FORMATTER_TO_PP(CLASS)  \
    template <> \
    struct fmt::formatter<CLASS> { \
      auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) { \
        auto it = ctx.begin(), ie = ctx.end(); \
        ENSURE(it == ie || *it == '}'); \
        return it; \
      } \
      template <typename FormatContext> \
      auto format(const CLASS& s, FormatContext& ctx) -> decltype(ctx.out()) { \
        return format_to(ctx.out(), "{}", euforia::pp::Pprint(s)); \
      } \
    }

#endif

