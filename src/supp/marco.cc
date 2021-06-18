#include "marco.h"

#include <boost/fusion/include/for_each.hpp>
#include <boost/algorithm/cxx11/iota.hpp>
#include <numeric>

#include "supp/pp/pp_std_instances.h"

using namespace std;

namespace {
int get_id(const z3::expr& e) {
  return e.hash();
}

z3::expr id2bool(z3::context& c, int i) {
  return c.bool_const(to_string(i).c_str());
}
}

namespace euforia {
namespace marco {

//^----------------------------------------------------------------------------^
//SubsetSolver methods
//
z3::expr SubsetSolver::CVar(int i) {
  if (auto search = varcache_.find(i); search == varcache_.end()) {
    stringstream name;
    name << constraints_[abs(i)];
    auto v = ctx().constant(name.str().c_str(), ctx().bool_sort());
    idcache_[get_id(v)] = i;
    if (i >= 0) {
      varcache_.insert({i, v});
    } else {
      varcache_.insert({i, !v});
    }
  }
  return varcache_.at(i);
}

SeedVector SubsetSolver::seed_from_core() {
  auto core = solver_.unsat_core();
  SeedVector seeds;
  boost::transform(core, back_inserter(seeds),
                   [&](auto&& b) { return idcache_.at(get_id(b)); });
  return seeds;
}

//! Attempts to shrink the current set of seeds. Erases each seed, one at a
//! time, updating the subset using the core if the subset is unsat.
SeedSet SubsetSolver::Shrink(const SeedVector& seed) {
  SeedSet current(seed);
  for (auto i : seed) {
    if (auto search = current.find(i); search == current.end()) {
      continue;
    }
    current.erase(i);
    logger.Log(6, "Shrink::CheckSubset({})", current);
    if (!CheckSubset(current)) {
      current = SeedSet(seed_from_core());
    } else {
      current.insert(i);
    }
  }
  return current;
}

//! Beginning with constraints not in `seed`, add them one at a time as long as
//! the constraints are satisfiable.
SeedVector SubsetSolver::Grow(const SeedVector& seed) {
  SeedVector current(seed);
  for (auto i : complement(current)) {
    current.push_back(i);
    if (!CheckSubset(current)) {
      current.pop_back();
    }
  }
  return current;
}

SeedSet SubsetSolver::complement(const SeedVector& s) const {
  SeedSet ret;
  boost::algorithm::iota_n(std::inserter(ret.s(), ret.s().end()), 0,
                           num_constraints());
  ret.erase(s);
  return ret;
}

//^----------------------------------------------------------------------------^
//MapSolver methods
//

MapSolver::MapSolver(z3::context& c, int n) : solver_(c) {
  boost::algorithm::iota_n(std::inserter(all_n_.s(), all_n_.s().end()),
                           0, n);
}

SeedSet MapSolver::complement(const SeedSet& s) const {
  SeedSet ret(all_n_);
  ret.erase(s);
  return ret;
}

//! Get the seed from the current model, if there is one (empty if not)
boost::optional<SeedVector> MapSolver::NextSeed() {
  if (solver_.check() == z3::check_result::unsat) {
    return boost::none;
  }
  SeedSet seed(all_n_);
  auto model = solver_.get_model();
  for (unsigned i = 0; i < model.size(); i++) {
    if (z3::eq(ctx().bool_val(false), model.eval(model[i]()))) {
      seed.erase(stoi(model[i].name().str()));
    }
  }
  SeedVector ret(seed.begin(), seed.end());
  return ret;
}

void MapSolver::BlockDown(const SeedSet& frompoint) {
  auto comp = complement(frompoint);
  z3::expr blocking(ctx());
  boost::transform(comp, ExprOrInserter(blocking),
                   [&](auto&& i) { return id2bool(ctx(), i); });
  solver_.add(blocking);
}

void MapSolver::BlockUp(const SeedSet& frompoint) {
  z3::expr blocking(ctx());
  boost::transform(frompoint, ExprOrInserter(blocking),
                   [&](auto&& i) { return !id2bool(ctx(), i); });
  solver_.add(blocking);
}


//^----------------------------------------------------------------------------^
//

// begin iterator constructor
MarcoEnumerator::Iterator::Iterator(
    Solver& s, const std::vector<z3::expr>& c)
    : ssolver_(SubsetSolver(s, c)), msolver_(MapSolver(s.ctx(), c.size())) {
  FindNextSupremalSet();
}

void MarcoEnumerator::Iterator::FindNextSupremalSet() {
  pp::DocStream s;
  s << "MarcoEnumerator::FindNextSupremalSet";
  assert(ssolver_);
  seed_ = msolver_->NextSeed();
  if (!seed_) {
    return;
  }
  auto pp_seed = pp::Pprint(*seed_);
  logger.Log(6, "{}", pp::group(s << ":" << pp::break_(1, 4) << pp_seed));

  if (ssolver_->CheckSubset(*seed_)) {
    auto mss = ssolver_->Grow(*seed_);
    last_subset_ = SupremalSet(Supremals::kMss, ssolver_->to_c_lits(mss));
    msolver_->BlockDown(mss);
  } else {
    auto mus = ssolver_->Shrink(*seed_);
    last_subset_ = SupremalSet(Supremals::kMus, ssolver_->to_c_lits(mus));
    msolver_->BlockUp(mus);
  }
}
} // end namespace marco
} // end namespace euforia
