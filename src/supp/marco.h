//! Comments taken from the python code in z3 at examples/python/mus/marco.py.
//! Implemented by Denis Bueno.
//!
//! Enumeration of Minimal Unsatisfiable Cores and Maximal Satisfying Subsets
//! This tutorial illustrates how to use Z3 for extracting all minimal
//! unsatisfiable cores together with all maximal satisfying subsets.
//!
//! Origin
//! The algorithm that we describe next represents the essence of the core
//! extraction procedure by Liffiton and Malik and independently by Previti and
//! Marques-Silva: Enumerating Infeasibility: Finding Multiple MUSes Quickly
//! Mark H. Liffiton and Ammar Malik in Proc. 10th International Conference on
//! Integration of Artificial Intelligence (AI) and Operations Research (OR)
//! techniques in Constraint Programming (CPAIOR-2013), 160-175, May 2013.
//!
//! Partial MUS Enumeration
//!  Alessandro Previti, Joao Marques-Silva in Proc. AAAI-2013 July 2013
//!
//! Z3py Features
//!
//! This implementation contains no tuning. It was contributed by Mark Liffiton
//! and it is a simplification of one of the versions available from his Marco
//! Polo Web site.  It illustrates the following features of Z3's Python-based
//! API:
//!    1. Using assumptions to track unsatisfiable cores.
//!    2. Using multiple solvers and passing constraints between them.
//!    3. Calling the C-based API from Python. Not all API functions are
//!       supported over the Python wrappers. This example shows how to get a
//!       unique integer identifier of an AST, which can be used as a key in a
//!       hash-table.
//!
//! Idea of the Algorithm
//! The main idea of the algorithm is to maintain two logical contexts and
//! exchange information between them:
//!
//!     1. The MapSolver is used to enumerate sets of clauses that are not
//!        already supersets of an existing unsatisfiable core and not already
//!        a subset of a maximal satisfying assignment. The MapSolver uses one
//!        unique atomic predicate per soft clause, so it enumerates sets of
//!        atomic predicates. For each minimal unsatisfiable core, say,
//!        represented by predicates
//!        p1, p2, p5, the MapSolver contains the clause  !p1 | !p2 | !p5. For
//!        each maximal satisfiable subset, say, represented by predicats p2,
//!        p3, p5, the MapSolver contains a clause corresponding to the
//!        disjunction of all literals not in the maximal satisfiable subset,
//!        p1 | p4 | p6.
//!     2. The SubsetSolver contains a set of soft clauses (clauses with the
//!        unique indicator atom occurring negated).  The MapSolver feeds it a
//!        set of clauses (the indicator atoms). Recall that these are not
//!        already a superset of an existing minimal unsatisfiable core, or a
//!        subset of a maximal satisfying assignment. If asserting these atoms
//!        makes the SubsetSolver context infeasible, then it finds a minimal
//!        unsatisfiable subset
//!        corresponding to these atoms. If asserting the atoms is consistent
//!        with the SubsetSolver, then it extends this set of atoms maximally
//!        to a satisfying set.
//!


#ifndef SUPP_MARCO_H_
#define SUPP_MARCO_H_

#include <boost/algorithm/cxx11/all_of.hpp>
#include <boost/iterator/iterator_facade.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/optional.hpp>
#include <boost/program_options.hpp>
#include <boost/range.hpp>
#include <boost/range/adaptor/indexed.hpp>
#include <boost/range/algorithm/copy.hpp>
#include <boost/range/algorithm/transform.hpp>
#include <boost/range/combine.hpp>
#include <fmt/format.h>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <z3++.h>


#include "checker_types.h" // tmeporary
#include "supp/expr_iterators.h"
#include "supp/expr_supp.h"
#include "supp/pp/doc.h"
#include "supp/solver.h"
#include "supp/std_supp.h"
#include "supp/z3_solver.h"

namespace euforia {
namespace marco {
using SeedVector = std::vector<int>;

//^----------------------------------------------------------------------------^

//! Represents a set of seeds (ints). I could have used a straight
//! unordered_set<int> for this, but I wrote this class so that I could have a
//! Range constructor. It also properly acts like a Boost Range.
class SeedSet {
 public:
  using iterator = std::unordered_set<int>::iterator;
  using const_iterator = std::unordered_set<int>::const_iterator;

  SeedSet() = default;

  template <typename Range>
  SeedSet(const Range& r) {
    boost::copy(r, std::inserter(s_, s_.end()));
  }

  size_t size() const { return s_.size(); }
  auto find(int i) const { return s_.find(i); }
  auto erase(int i) { return s_.erase(i); }
  template <typename Range>
  void erase(Range&& r) {
    for (auto&& i : r) {
      s_.erase(i);
    }
  }
  auto insert(int i) { return s_.insert(i); }

  iterator begin() { return s_.begin(); }
  iterator end() { return s_.end(); }
  const_iterator begin() const { return s_.begin(); }
  const_iterator end() const { return s_.end(); }

  std::unordered_set<int>& s() { return s_; }

 private:
  std::unordered_set<int> s_;
};

//^----------------------------------------------------------------------------^

//! Solves subsets of a given set of constraints, allowing growing and
//! shrinking. For a given set of constraints, it asserts a formula (c_i =>
//! <constraint i>), where c_i is a Boolean indicator variable.
class SubsetSolver {
 public:
  SubsetSolver(Solver& s) : solver_(s) {}

  template <typename Range>
  SubsetSolver(Solver& s, const Range& r) : solver_(s) {
    boost::copy(r, back_inserter(constraints_));
    for (size_t i = 0; i < num_constraints(); i++) {
      solver_.Add(z3::implies(CVar(i), constraints_[i]));
    }
  }

  template <typename Range>
  bool CheckSubset(const Range& seeds) {
    z3::expr_vector assumptions(ctx());
    boost::transform(seeds, ExprVectorInserter(assumptions),
                     [&](auto&& seed) { return CVar(seed); });
    auto result = solver_.Check(assumptions) == CheckResult::kSat;

    logger.Log(6, "SubsetSolver::CheckSubset => {}",
               result == true ? "sat" : "unsat");
    return result;
  }

  size_t num_constraints() const { return constraints_.size(); }

  z3::context& ctx() const { return solver_.ctx(); }

  SeedVector seed_from_core();

  //! Returns the actual constraint
  template <typename Range>
  std::vector<z3::expr> to_c_lits(const Range& seed) {
    std::vector<z3::expr> ret;
    boost::transform(seed, back_inserter(ret),
                     [&](auto&& i) { return constraints_.at(i); });
    return ret;
  }

  SeedSet Shrink(const SeedVector&);

  SeedVector Grow(const SeedVector&);

 private:
  friend class MarcoEnumerator;
  std::vector<z3::expr> constraints_; // could be const after constructer
  Solver& solver_;
  // Boolean vars by index
  std::unordered_map<int, z3::expr> varcache_;
  // Maps constraint id to int in varcache_
  std::unordered_map<unsigned, int> idcache_;

  z3::expr CVar(int i);

  SeedSet complement(const SeedVector&) const;

};

//^----------------------------------------------------------------------------^

//! Solves a set of Boolean variables -- is there a way to tell a Z3 solver I'm
//! only going to be solving SAT problems?
class MapSolver {
 public:
  //! n - number of constraints to map, indexed 0 to n-1
  MapSolver(z3::context& c, int n);

  boost::optional<SeedVector> NextSeed();

  //! Blocks down from a given set
  void BlockDown(const SeedSet& frompoint);

  //! Blocks up from a given set
  void BlockUp(const SeedSet& frompoint);

  z3::context& ctx() const { return solver_.ctx(); }

 private:
  z3::solver solver_;
  SeedSet all_n_;

  SeedSet complement(const SeedSet&) const;
};

//^----------------------------------------------------------------------------^

//! Enumerate minimal unsatisfiable subsets (MUSes) and maximal satisfiable
//! subsets (MSSes) using the MARCO algorithm.
class MarcoEnumerator {
 public:
  enum class Supremals { kMus, kMss };

  class Iterator;

  //! A set of constraints that are either a MUS or a MSS
  class SupremalSet {
   public:
    using iterator = std::vector<z3::expr>::iterator;
    using const_iterator = std::vector<z3::expr>::const_iterator;

    SupremalSet(Supremals kind, std::vector<z3::expr>&& s)
        : kind_(kind), subset_(s) {}

    Supremals kind() const { return kind_; }
    const std::vector<z3::expr>& subset() const { return subset_; }
    auto begin() const { return subset_.begin(); }
    auto end() const { return subset_.end(); }

   private:
    Supremals kind_;
    std::vector<z3::expr> subset_;

    friend class Iterator;
    // kind is uninitialized so don't do anything with this
    SupremalSet() {}
  };


  //! This iterator is expensive to copy.
  class Iterator : public boost::iterator_facade<
      Iterator, const SupremalSet, boost::forward_traversal_tag> {
   public:
    // end iterator has no seed or solver
    Iterator() = default;
    // initializes seed_ with solver
    Iterator(
        Solver& s, const std::vector<z3::expr>& constraints);

   private:
    // end() iterator has none everywhere
    boost::optional<SubsetSolver> ssolver_;
    boost::optional<MapSolver> msolver_;
    boost::optional<SeedVector> seed_; // empty = end
    // last subset returned by FindNextSupremalSet
    SupremalSet last_subset_;

    friend class boost::iterator_core_access;

    void increment() { FindNextSupremalSet(); }
    bool equal(const Iterator& other) const { return seed_ == other.seed_; }
    const SupremalSet& dereference() const { return last_subset_; }

    void FindNextSupremalSet();
  };

  using iterator = Iterator;
  using const_iterator = const Iterator;

  //! Solver argument is used for solving constraint subsets
  template <typename Range>
  MarcoEnumerator(Solver& s, const Range& constraints) : solver_(s) {
    boost::copy(constraints, back_inserter(constraints_));
  }

  iterator begin() { return Iterator(solver_, constraints_); }

  iterator end() { return Iterator(); }

 private:
  Solver& solver_;
  std::vector<z3::expr> constraints_;
};

} // end namespace marco

template <>
struct euforia::pp::PrettyPrinter<marco::SeedSet> {
  euforia::pp::DocPtr operator()(const marco::SeedSet& s) const {
    auto g = pp::commabox(s.begin(), s.end(), pp::text(","));
    pp::DocStream d;
    d << "SeedSet<" << pp::nest(4, g) << ">";
    return d;
  }
};

template <>
struct euforia::pp::PrettyPrinter<marco::MarcoEnumerator::Supremals> {
  euforia::pp::DocPtr operator()(const marco::MarcoEnumerator::Supremals& s) const {
    switch (s) {
      case marco::MarcoEnumerator::Supremals::kMss:
        return pp::text("MSS");
      case marco::MarcoEnumerator::Supremals::kMus:
        return pp::text("MUS");
      default:
        break;
    }
    EUFORIA_FATAL("unhandled switch case");
  }
};

template <>
struct euforia::pp::PrettyPrinter<marco::MarcoEnumerator::SupremalSet> {
  euforia::pp::DocPtr operator()(const marco::MarcoEnumerator::SupremalSet& s) const {
    auto g = pp::commabox(s.begin(), s.end(), pp::text(","));
    pp::DocStream d;
    d << pp::Pprint(s.kind()) << "<" << pp::nest(4, g) << ">";
    return d;
  }
};

} // end namespace euforia

EUFORIA_FWD_FORMATTER_TO_PP(euforia::marco::SeedSet);
EUFORIA_FWD_FORMATTER_TO_PP(euforia::marco::MarcoEnumerator::Supremals);
EUFORIA_FWD_FORMATTER_TO_PP(euforia::marco::MarcoEnumerator::SupremalSet);

#endif
