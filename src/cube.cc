// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "cube.h"

#include <boost/container_hash/hash.hpp>
#include <boost/range/algorithm/copy.hpp>
#include <algorithm>

#include "supp/expr_supp.h"

using namespace std;

namespace euforia {
  
  static uint64_t cubeCounter = 0;

  // constructors

  Cube::Cube(z3::context& c) 
      : ctx_(c), hashval(0), dirty(1), ID(cubeCounter++) {}
  
  Cube::Cube(const Cube& src) :
      ctx_(src.ctx_), lits(src.lits), next(src.next), hashval(src.hashval),
      dirty(src.dirty), ID(cubeCounter++)
#ifdef CUBE_HISTORY
      ,history(src.history)
#endif
  {}
  
  Cube::Cube(Cube&& src) : ctx_(src.ctx_) {
    std::swap(lits, src.lits);
    std::swap(next, src.next);
    hashval = src.hashval;
    dirty = src.dirty;
    std::swap(ID, src.ID);
#ifdef CUBE_HISTORY
    std::swap(history, src.history);
#endif
  }

  Cube::Cube(const Cube& src, const z3::expr& without) 
      : ctx_(src.ctx_), next(src.next), hashval(0), dirty(1),
      ID(cubeCounter++) {
    next.erase(without);
    lits.reserve(src.lits.size()-1);
    auto& srcLits = src.lits;
    for (size_t i = 0; i < srcLits.size(); i++) {
      if (!z3::eq(without, srcLits[i])) {
        lits.push_back(srcLits[i]);
      }
    }
  }

  /*-----------------------------------------------------------------------------------*/
    
  void Cube::recomputeHash() const {
    hashval = boost::hash_range(begin(), end());
    dirty = 0;
  }

  
  
  Cube::iterator Cube::begin() { return Cube::iterator(this, 0); }
  Cube::iterator Cube::end() { return Cube::iterator(this, lits.size()); }
  Cube::const_iterator Cube::begin() const { return Cube::const_iterator(lits.begin()); }
  Cube::const_iterator Cube::end() const { return Cube::const_iterator(lits.end()); }
  
  Cube::next_state_iterator Cube::nbegin() { return Cube::next_state_iterator(next.begin()); }
  Cube::next_state_iterator Cube::nend() { return Cube::next_state_iterator(next.end()); }
  Cube::const_next_state_iterator Cube::nbegin() const { return Cube::const_next_state_iterator(next.begin()); }
  Cube::const_next_state_iterator Cube::nend() const { return Cube::const_next_state_iterator(next.end()); }
  

  
  void Cube::push(const z3::expr& c, const z3::expr& n) {
    dirty = 1;
    assert(IsLiteral(c));
    if (!contains(c)) {
      assert(IsLiteral(n));
      if (!z3::eq(c, c.ctx().bool_val(true))) {
        lits.emplace_back(c);
        next.emplace(c, n);
      }
    }
  }

  void Cube::swap(Cube& other) {
    assert(&ctx() == &other.ctx());
    lits.swap(other.lits);
    next.swap(other.next);
    dirty = 1;
#ifdef CUBE_HISTORY
    history.swap(other.history);
#endif
    std::swap(ID, other.ID);
  }
  
    
  z3::expr Cube::asExpr() const {
    return expr_mk_and(ctx(), begin(), end());
  }
  
  z3::expr Cube::asExprNext() const {
    auto it = lits.begin();
    const auto ie = lits.end();
    assert(it != ie);
    auto ret = getNext(*it++);
    while (it != ie) {
      ret = ret && getNext(*it++);
    }
    return ret;
  }
  
  z3::expr Cube::negation() const {
    auto it = lits.begin();
    const auto ie = lits.end();
    assert(it != ie);
    auto ret = expr_not(*it++);
    while (it != ie) {
      ret = ret || expr_not(*it++);
    }
    return ret;
  }
  
  z3::expr Cube::negationNext() const {
    auto it = lits.begin();
    const auto ie = lits.end();
    assert(it != ie);
    auto ret = expr_not(getNext(*it++));
    while (it != ie) {
      ret = ret || expr_not(getNext(*it++));
    }
    return ret;
  }
    
  
  void Cube::sort() {
    auto comp = [](const z3::expr& l, const z3::expr& r) {
      auto hl = l.hash();
      auto hr = r.hash();
      return hl < hr;
    };
    std::stable_sort(lits.begin(), lits.end(), comp);
  }
  
  
  /*-----------------------------------------------------------------------------------*/
  
  std::size_t TimedCube::hash() const {
    size_t hash = thecube->hash();
    boost::hash_combine(hash, frame);
    return hash;
  }

}
