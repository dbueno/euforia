// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "one_hot.h"

#include <boost/optional.hpp>
#include <boost/variant.hpp>
#include <boost/variant/recursive_variant.hpp>
#include <numeric>

#include "supp/expr_supp.h"
#include "supp/std_supp.h"


using namespace std;


namespace euforia {

#ifdef BOOST_VARIANT_NO_FULL_RECURSIVE_VARIANT_SUPPORT
#error "error: euforia uses recursive variants"
#endif

// Recursive variant type for a (nested) list of "subordinates"
using Subord = boost::make_recursive_variant<
    z3::expr, vector<boost::recursive_variant_>>::type;

//^----------------------------------------------------------------------------^
// Impl
class OneHotConstraints::Impl {
  friend class OneHotConstraints;
 public:
  Impl(z3::context& c) : ctx_(c) {}

  z3::context& ctx() const { return ctx_; }

  z3::expr CmdrAtMostOne(const std::vector<Subord>& subords,
                         boost::optional<z3::expr> cmdr_var);
  z3::expr CmdrAtMostOne(const vector<Subord>& subords);

 private:
  z3::context& ctx_;
  ExprSet cmdr_vars_;

  z3::expr FreshVar() {
    auto b = FreshBool(ctx(), "cmdr");
    cmdr_vars_.insert(b);
    return b;
  }
};

//^----------------------------------------------------------------------------^
// Get rid of this

// XXX this looks like a case for variant<>
// variant<ListOfVar, Var>
class subord {
 public:
  enum class kind { List, Var };
  const enum kind kind;

  virtual z3::expr getVar() const = 0;

  subord(const subord&) = delete;
  void operator=(const subord&) = delete;

  virtual ~subord() = default;

 protected:
  subord(enum kind k) : kind(k) {}
};

class subord_var final : public subord {
  z3::expr var;
 public:
  subord_var(const z3::expr& v) : var(v), subord(subord::kind::Var) {}
  z3::expr getVar() const override { return var; }
};

class subord_list  final : public subord {
 public:
  vector<std::unique_ptr<subord>> elements;
  subord_list() : subord(subord::kind::List) {}
  z3::expr getVar() const override { throw invalid_argument("subord_list has no var"); }
  void push(const z3::expr& lit) {
    auto t = std::make_unique<subord_var>(lit);
    elements.push_back(move(t));
  }
  size_t size() const { return elements.size(); }
};

static vector<z3::expr> NaiveAtMostOne(const subord_list& subords) {
  vector<z3::expr> ret;
  auto& xs = subords.elements;
  for (size_t i = 0; i < xs.size(); i++) {
    vector<z3::expr> group;
    for (size_t j = i+1; j < xs.size(); j++) {
      group.push_back(!xs[i]->getVar() || !xs[j]->getVar());
    }
    if (group.size() > 0)
      ret.push_back(std::accumulate(begin(group), end(group), group[0].ctx().bool_val(true), expr_and));
  }
  return ret;
}


// precondition: vars only contains variables, no lists
// precondition: vars.size() > 0
static z3::expr NaiveAtMostOne(const vector<Subord>& vars) {
  z3::expr_vector v(boost::get<z3::expr>(vars[0]).ctx());
  ExprVectorInserter out(v);
  for (size_t i = 0; i < vars.size(); i++) {
    for (size_t j = i+1; j < vars.size(); j++) {
      auto vi = boost::get<z3::expr>(vars[i]),
           vj = boost::get<z3::expr>(vars[j]);
      *out++ = expr_not(vi) || expr_not(vj);
    }
  }
  return expr_mk_and(v);
}


// Groups the given list a variables in a nested list. Each (nested) result
// sublist has at most max_size elements.
static vector<Subord> GroupVars(const vector<Subord>& vars, size_t max_size) {
  const auto num_vars = vars.size();
  if (num_vars <= max_size) {
    return vars;
  } else {
    vector<Subord> ret;
    size_t num_groups = num_vars / max_size;
    const size_t group_size = num_vars / num_groups;
    auto it = vars.begin();
    for (size_t i = 0; i < num_groups; i++) {
      vector<Subord> sub;
      for (size_t j = 0; j < group_size; j++) {
        sub.push_back(*it++);
      }
      ret.push_back(sub);
    }
    // put rest of elements onto last group
    if (!ret.empty()) {
      auto *last_group = boost::get<vector<Subord>>(&ret.back());
      auto ie = vars.end();
      while (it != ie) {
        last_group->push_back(*it++);
      }
    }
    return GroupVars(ret, max_size);
  }
}
  

//^----------------------------------------------------------------------------^
//OneHotConstraints

OneHotConstraints::OneHotConstraints(z3::context& c) 
    : pimpl_(std::make_unique<Impl>(c)) {}

OneHotConstraints::OneHotConstraints(const OneHotConstraints& c)
    : pimpl_(std::make_unique<Impl>(*c.pimpl_)) {}
  
OneHotConstraints& OneHotConstraints::operator=(OneHotConstraints&& c) {

  swap(pimpl_, c.pimpl_);
  return *this;
}
 
OneHotConstraints::~OneHotConstraints() = default;

z3::expr OneHotConstraints::Impl::CmdrAtMostOne(
    const vector<Subord>& subords, boost::optional<z3::expr> cmdr_var) {
  z3::expr_vector v(ctx());
  ExprVectorInserter phi_out(v);
  vector<Subord> clause_vars;
  for (auto&& s : subords) {
    if (const z3::expr *var = boost::get<z3::expr>(&s)) {
      clause_vars.push_back(*var);
    } else if (const vector<Subord>* nested_subord =
               boost::get<vector<Subord>>(&s)) {
      auto subord_var = FreshVar();
      clause_vars.push_back(subord_var);
      *phi_out++ = CmdrAtMostOne(*nested_subord, subord_var);
    }
  }
  // if cmdr_var != 0 -- this means the variable SAT *number* is 0
  // then clause_vars += !cmdr_var; huh?!?!?
  if (cmdr_var) {
    clause_vars.push_back(!*cmdr_var);
  }
  *phi_out++ = NaiveAtMostOne(clause_vars);
  return expr_mk_and(v);
}

z3::expr OneHotConstraints::Impl::CmdrAtMostOne(const vector<Subord>& subords) {
  // XXX the called function here should fill a set with the introduced
  // variables, then the pair of the constraints and the set should be returned
  return CmdrAtMostOne(subords, boost::optional<z3::expr>());
}


const ExprSet& OneHotConstraints::commander_vars() const {
  return pimpl_->cmdr_vars_;
}


z3::expr OneHotConstraints::at_most(
    const OneHotConstraints::Config& c) {
  switch (c.encoding_type) {
    case OneHotConstraints::Config::kCommander: {
      vector<Subord> subords_in(bools.begin(), bools.end());
      auto subords = GroupVars(subords_in, c.commander_max_size);
      return pimpl_->CmdrAtMostOne(subords);
    }
    
    case OneHotConstraints::Config::kNaive: {
      return expr_mk_and(ctx(), constraintsAtMost());
    }
  }
  EUFORIA_FATAL("encoding_type switch not exhaustive");
}


static z3::expr NaiveAtLeastOne(const subord_list& subords) {
  assert(subords.size() > 0);
  z3::expr ret = subords.elements[0]->getVar();
  for (size_t i = 1; i < subords.size(); i++) {
    auto& elt = subords.elements[i];
    ret = ret || elt->getVar();
  }
  return ret;
}

static vector<z3::expr> NaiveExactlyOne(const subord_list& subords) {
  vector<z3::expr> atMost = NaiveAtMostOne(subords);
  z3::expr atLeast = NaiveAtLeastOne(subords);
  atMost.push_back(atLeast);
  return atMost;
}



#if 0


static vector<z3::expr> CmdrExactlyOne(subord_list Subords, const z3::expr& CmdrVar) {
  vector<z3::expr> clauses; // to return
  vector<subord> clauseVars;
  clauseVars.reserve(1000);

  for (int i = 0; i < Subords.elements.size(); i++) {
    auto& elt = Subords.elements[i];
    switch (elt.kind) {
      case subord::kind::Var:
        clauseVars[i] = elt;
        break;

      case subord::kind::List: {
        clauseVars[i] = subord_var(freshBool());
        for (auto& clause : CmdrExactlyOne(elt, clauseVars[i])) {
          clauses.push_back(clause);
        }
      }
    }
  }

  // maybe negate CmdrVar?

  clauses.push_back(NaiveExactlyOne(ClauseVars));

  return clauses;

}




static vector<z3::expr> CmdrExactlyOne(subord_list Subords) {
  return CmdrExactlyOne(GroupVars(Subords), freshBool());
}

#endif

std::vector<z3::expr> OneHotConstraints::constraintsExactly() const {
  vector<z3::expr> formulas;
  subord_list currs;
  for (const auto& var : bools) {
    currs.push(var);
  }
  auto currClauses = NaiveExactlyOne(currs);
  formulas.insert(formulas.end(), begin(currClauses), end(currClauses));
  return formulas;
}


vector<z3::expr> OneHotConstraints::constraintsAtMost() const {
  //#define USE_COMMANDER_ONE_HOT
#ifdef USE_COMMANDER_ONE_HOT
  vector<z3::expr> boolvec(bools.begin(), bools.end());
  auto ret = cmdrAtMostOne(boolvec.size(), boolvec.begin(), boolvec.end());
  return ret.second;
#else
  vector<z3::expr> formulas;
  subord_list currs;
  for (const auto& var : bools) {
    currs.push(var);
  }
  auto currClauses = NaiveAtMostOne(currs);
  formulas.insert(formulas.end(), begin(currClauses), end(currClauses));
  return formulas;
#endif
}

}
