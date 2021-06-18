// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef cube_hpp
#define cube_hpp

#include <boost/container_hash/hash_fwd.hpp>
#include <cassert>
#include <functional>
#include <iterator>
#include <memory>
#include <vector>

#include "supp/std_supp.h"
#include "supp/expr_supp.h"
#include "supp/pp/doc.h"

namespace euforia {


/*
 * A cube represents a set of literals.
 */
class Cube {
 public:
  using lit_storage = std::vector<z3::expr>;
  using next_state_map = ExprMap<z3::expr>;

 private:

  z3::context& ctx_;
  lit_storage lits;

  //we need this precomputed so that the next state cube is computed only once
  next_state_map next; // maps lit to its next state version (ie, all variables plus'd)

  mutable uint64_t hashval:63;
  mutable uint64_t dirty:1;

  void recomputeHash() const;

 public:

#ifdef CUBE_HISTORY
  // stack tracing origin of this cube (earlier frames it's been in)
  std::vector<int> history;
#endif

  uint64_t ID;

  Cube(z3::context&);
  // same as src Cube without lit
  Cube(const Cube& src, const z3::expr& without);
  Cube(const Cube& src);
  Cube(Cube&& src);

  inline z3::context& ctx() const { return ctx_; }

  inline bool operator==(const Cube& rhs) const {
    if (size() != rhs.size())
      return false;

    for (size_t i = 0; i < size(); i++) {
      const z3::ExprWrapper ith = (*this)[i];
      const z3::ExprWrapper rhs_ith = rhs[i];
      if (ith != rhs_ith)
        return false;
    }

    return true;
  }

  inline z3::expr& operator[](const size_t i) { return lits[i]; }
  inline const z3::expr& operator[](const size_t i) const { return lits[i]; }

  inline size_t hash() const {
    if (dirty)
      recomputeHash();
    return hashval;
  }

  inline z3::expr erase(const size_t i) {
    dirty = 1;
    auto ret = lits[i];
    next.erase(ret);
    if (lits.size() > 1)
      lits[i] = lits.back();
    lits.pop_back();
    return ret;
  }

  /// Whether this cube contains the given literal
  inline bool contains(const z3::expr& l) const { return next.find(l) != next.end(); }

  inline z3::expr getNext(const z3::expr& l) const { return next.at(l); }

  inline bool empty() const { return lits.empty(); }

  inline size_t size() const { return lits.size(); }

  inline bool subsumes(const Cube &other) const {
    return all_of(lits.begin(), lits.end(), [&](const z3::expr& l) {
                  return other.contains(l); });
  }


  /**
   * Returns all the literals AND'd together.
   */
  z3::expr asExpr() const;

  /**
   * Returns all next-state literals AND'd together.
   */
  z3::expr asExprNext() const;

  /**
   * Returns an sol_expression that is equivalent to the negation if this cube. If
   * the cube is empty, will fail with an assertion error.
   */
  z3::expr negation() const;

  /**
   * Same as negation but uses next-state variables.
   */
  z3::expr negationNext() const;

  void sort();


  void push(const z3::expr& lcurr, const z3::expr& lnext);    

  class iterator {
   private:
    Cube *c; // ptr so I get copy-assign
    size_t i; // 0-lits.size

   public:
    typedef iterator self_type;
    typedef z3::expr value_type;
    typedef const z3::expr& reference;
    typedef z3::expr* pointer;
    typedef std::forward_iterator_tag iterator_category;
    typedef int difference_type;
    iterator(Cube *c, size_t start) : c(c), i(start) { assert(c); }
    inline self_type operator++() { ++i; return *this; }
    inline self_type operator++(int) { self_type it(c, i); ++*this; return it; }
    inline reference operator*() { return c->lits[i]; }
    /// Erases current element, swaps with last
    inline self_type erase() {
      c->dirty = 1;
      auto lit = c->lits[i];
      c->next.erase(lit);
      c->lits[i] = c->lits.back();
      c->lits.pop_back();
      assert(c->next.size() == c->lits.size());
      assert(i <= c->lits.size());
      //        if (i == c->lits.size() && i > 0) {
      //          return self_type(c, --i);
      //        }
      return *this;
    }
    inline void replace(const z3::expr& cur, const z3::expr& nxt) {
      c->dirty = 1;
      assert(IsLiteral(cur));
      assert(IsLiteral(nxt));
      c->next.erase(c->lits[i]);
      c->lits[i] = cur;
      c->next.insert({cur, nxt});
    }
    bool operator==(const self_type& rhs) const { return i == rhs.i; }
    bool operator!=(const self_type& rhs) const { return i != rhs.i; }
  };

  iterator begin();
  iterator end();


  class const_iterator {
   private:
    lit_storage::const_iterator it;

   public:
    typedef const_iterator self_type;
    typedef z3::expr value_type;
    typedef const z3::expr& reference;
    typedef z3::expr* pointer;
    typedef std::forward_iterator_tag iterator_category;
    typedef int difference_type;
    const_iterator(lit_storage::const_iterator start) : it(start) {}
    inline self_type operator++() { ++it; return *this; }
    inline self_type operator++(int) { self_type i = *this; ++it; return i; }
    self_type operator --() { --it; return *this; }
    self_type operator --(int) { self_type i = *this; --it; return i; }
    inline reference operator*() const { return *it; }
    bool operator==(const self_type& rhs) const { return it == rhs.it; }
    bool operator!=(const self_type& rhs) const { return it != rhs.it; }
  };

  const_iterator begin() const;
  const_iterator end() const;


  /**
   * Iterate over the literals in the cube, but each state variable uses its next-state version.
   */
  class next_state_iterator
  {
   private:
    next_state_map::iterator it;

   public:
    typedef next_state_iterator self_type;
    typedef z3::expr value_type;
    typedef const z3::expr& reference;
    typedef z3::expr* pointer;
    typedef std::forward_iterator_tag iterator_category;
    typedef int difference_type;
    next_state_iterator(next_state_map::iterator start) : it(start) {}
    self_type operator++() { ++it; return *this; }
    self_type operator++(int) { self_type i = *this; ++it; return i; }
    reference operator*() { return (*it).second; }
    bool operator==(const self_type& rhs) { return it == rhs.it; }
    bool operator!=(const self_type& rhs) { return it != rhs.it; }
  };

  next_state_iterator nbegin();
  next_state_iterator nend();

  class const_next_state_iterator
  {
   private:
    next_state_map::const_iterator it;

   public:
    typedef const_next_state_iterator self_type;
    typedef z3::expr value_type;
    typedef const z3::expr& reference;
    typedef const z3::expr* pointer;
    typedef std::forward_iterator_tag iterator_category;
    typedef int difference_type;
    const_next_state_iterator(next_state_map::const_iterator start) : it(start) {}
    self_type operator++() { ++it; return *this; }
    self_type operator++(int) { self_type prev = *this; ++it; return prev; }
    reference operator*() { return (*it).second; }
    bool operator==(const self_type& rhs) { return it == rhs.it; }
    bool operator!=(const self_type& rhs) { return it != rhs.it; }
  };

  const_next_state_iterator nbegin() const;
  const_next_state_iterator nend() const;

};
  
  



  /**
   * Timed cube. Contains a cube and a frame.
   */
class TimedCube {
 public:
  std::shared_ptr<Cube> thecube;
  int frame; // negative & positive used

  TimedCube(int frame) : frame(frame) {}
  TimedCube(std::shared_ptr<class Cube> Cube, int frame) 
      : thecube(std::move(Cube)), frame(frame) {}
  TimedCube(TimedCube& t, int frame) : thecube(t.thecube), frame(frame) {}
  TimedCube(TimedCube&& t, int frame) : thecube(t.thecube), frame(frame) {}

  //! Whether this TimedCube has a cube
  operator bool() const {
    return bool(thecube);
  }

  /**
   * Returns a TimedCube with the same cube and frame+1.
   */
  inline TimedCube next() const { return TimedCube(thecube, frame+1); }

  std::size_t hash() const;

  inline bool operator==(const TimedCube& rhs) const {
    return thecube == rhs.thecube && frame == rhs.frame;
  }

  inline bool operator!=(const TimedCube& rhs) const {
    return !(*this == rhs);
  }
};
    
struct TimedCubeHash {
  inline std::size_t operator()(const TimedCube& k) const {
    return k.hash();
  }
};

struct TimedCubeEqualTo {
  inline bool operator()(const TimedCube& lhs, const TimedCube& rhs) const {
    return lhs == rhs;
  }
};


template<class T>
using tcube_umap = std::unordered_map<TimedCube, T, TimedCubeHash,
      TimedCubeEqualTo>;

template <>
struct euforia::pp::PrettyPrinter<Cube> {
  euforia::pp::DocPtr operator()(const Cube& c) {
    auto g = pp::groupsep(
        c.begin(), c.end(),
        pp::group(pp::append(
                pp::break_(1, 0),
                pp::append(pp::text(AcSep(Z3_OP_AND)), pp::text(" ")))));
    pp::DocStream s;
    s << "cube<" << pp::nest(4, g) << ">";
    return s;
  }
};

template <>
struct euforia::pp::PrettyPrinter<TimedCube> {
  euforia::pp::DocPtr operator()(const TimedCube& c) {
    auto g = pp::groupsep(
        c.thecube->begin(), c.thecube->end(),
        pp::group(pp::append(
                pp::break_(1, 0),
                pp::append(pp::text(AcSep(Z3_OP_AND)), pp::text(" ")))));
    pp::DocStream s;
    s << "tcube@" << std::to_string(c.frame) << pp::text("<")
        << pp::nest(4, g) << ">";
    return s;
  }
};

} // namespace euforia

template <>
struct fmt::formatter<euforia::Cube> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), ie = ctx.end();
    ENSURE(it == ie || *it == '}');
    return it;
  }

  template <typename FormatContext>
  auto format(const euforia::Cube& c, FormatContext& ctx) -> decltype(ctx.out()) {
    return format_to(ctx.out(), "{}", euforia::pp::Pprint(c));
  }
};

template <>
struct fmt::formatter<euforia::TimedCube> {
  auto parse(format_parse_context& ctx) -> decltype(ctx.begin()) {
    auto it = ctx.begin(), ie = ctx.end();
    ENSURE(it == ie || *it == '}');
    return it;
  }

  template <typename FormatContext>
  auto format(const euforia::TimedCube& c, FormatContext& ctx) -> decltype(ctx.out()) {
    return format_to(ctx.out(), "{}", euforia::pp::Pprint(c));
  }
};

void mylog(const euforia::Cube& c);
void mylog(const euforia::TimedCube& t);

#endif

