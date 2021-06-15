// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_LAYERED_REFINEMENT_H_
#define EUFORIA_LAYERED_REFINEMENT_H_

#include "checker_types.h"
#include "supp/boolector_solver.h"
#include "supp/expr_iterators.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_supp.h"
#include "supp/expr_visitor.h"
#include "supp/solver.h"
#include "supp/statistics.h"

namespace euforia {

class Arrays2Uf : public ExprRewriter<Arrays2Uf>,
    public ExprVisitor<Arrays2Uf, z3::expr> {

 public:
  Arrays2Uf(z3::context& c) 
      : ctx_(c), num_arrays_(0) {}

  z3::expr operator()(const z3::expr& e) { return Rewrite(e); }

  z3::expr_vector operator()(const z3::expr_vector& es) {
    z3::expr_vector out(ctx_);
    for (unsigned i = 0; i < es.size(); i++) {
      out.push_back((*this)(es[i]));
    }
    return out;
  }

  z3::expr visitExpr(const z3::expr& e) {
    if (e.get_sort().is_array()) {
      num_arrays_++;
    }
    return e.decl()(NewArgsExprVector(e));
  }

  z3::expr visitSTORE(const z3::expr& e) {
    assert(e.num_args()==3);
    if (abstract_arrays_) {
      std::function<z3::expr(const z3::expr_vector&)> decl =
          [](const z3::expr_vector& args) {
            assert(args.size() == 3);
            return z3::store(args[0], args[1], args[2]);
          };
      return AbstractUfIntParams("STORE", e, decl);
    } else {
      auto ret = z3::store(Arg(e,0), Arg(e,1), Arg(e,2));
      return ret;
    }
  }

  z3::expr visitSELECT(const z3::expr& e) {
    assert(e.num_args()==2);
    if (abstract_arrays_) {
      std::function<z3::expr(const z3::expr_vector&)> decl =
          [](const z3::expr_vector& args) {
            assert(args.size() == 2);
            return z3::select(args[0], args[1]);
          };
      return AbstractUfIntParams("SELECT", e, decl);
    } else {
      return z3::select(Arg(e,0), Arg(e,1));
    }
  }

  z3::expr visitCONST_ARRAY(const z3::expr& e) {
    std::function<z3::expr(const z3::expr_vector&)> decl =
        [e](const z3::expr_vector& args) {
          // XXX this doesn't handle the case where abstract_arrays_ is false
          assert(args.size() == 2);
          auto sort = e.get_sort().array_domain();
          return z3::const_array(sort, args[1]);
        };
    if (abstract_arrays_) {
      return AbstractUfIntParams("CONST-ARRAY", e, decl);
    } else {
      auto abs = 
          z3::const_array(AbstractSort(e.get_sort().array_domain()), Arg(e,0));
      return abs;
    }
  }

  int64_t num_arrays() const { return num_arrays_; }

 private:
  const bool abstract_arrays_ = true;
  z3::context& ctx_;
  // int64_t unique_counter_;
  int64_t num_arrays_;

  
  // Returns an uninterpreted function/predicate based on given name and
  // applies it to args
  z3::expr AbstractUf(const std::string& name,
                      const z3::expr& n,
                      z3::sort sort,
                      std::function<z3::expr(const z3::expr_vector&)> /*decl*/,
                      const z3::expr_vector& args) {
    z3::sort_vector sorts(ctx_);
    z3::sort retSort = AbstractSort(sort);
    for (unsigned i = 0; i < args.size(); i++) {
      sorts.push_back(args[i].get_sort());
    }
    std::stringstream nameStream;
    nameStream << name;
    for (unsigned i = 0; i < args.size(); i++) {
      nameStream << "_" << SortName(n.arg(i).get_sort());
    }
    auto f = ctx_.function(nameStream.str().c_str(), sorts, retSort);
    return f(args);
  }

  // Uses name as the basis for the UF name. e is the concrete expression for
  // which you're creating a UF application.
  z3::expr AbstractUfIntParams(
      const std::string& name, const z3::expr& e,
      std::function<z3::expr(const z3::expr_vector&)> /*conc_decl*/);

  z3::sort AbstractSort(const z3::sort& s) const {
    if (s.is_bool()) return s;

    else if (s.is_array()) {
      if (abstract_arrays_) {
        // turn into its own uninterpreted sort
        return s.ctx().uninterpreted_sort(
            (uninterpreted_array_sort_name + SortName(s)).c_str());
      } else {
        // turn into term->term array, not supported by ANY LOGIC EVER
        auto domsort = s.array_domain();
        auto rasort = s.array_range();
        return s.ctx().array_sort(AbstractSort(domsort), AbstractSort(rasort));
      }
    } else {
      return s.ctx().uninterpreted_sort((uninterpreted_bv_sort_name + 
                                         std::to_string(s.bv_size())).c_str());
    }
  }
};

//^----------------------------------------------------------------------------^

//! Abstracts a concrete formula by turning array reads and writes into fresh
//! variables that don't share any constraints with one another.
class Arrays2Fresh : public ExprRewriter<Arrays2Fresh>,
    public ExprVisitor<Arrays2Fresh, z3::expr> {

 public:
  Arrays2Fresh(z3::context& c) 
      : ctx_(c), unique_counter_(0), num_arrays_(0) {}

  z3::expr operator()(const z3::expr& e) { return Rewrite(e); }
  z3::expr_vector operator()(const z3::expr_vector& es);

  z3::expr visitExpr(const z3::expr& e);
  z3::expr visitUNINTERPRETED(const z3::expr& e);
  z3::expr visitSTORE(const z3::expr& e);
  z3::expr visitSELECT(const z3::expr& e);
  z3::expr visitCONST_ARRAY(const z3::expr& e);

  int64_t num_arrays() const { return num_arrays_; }

 private:
  const bool abstract_arrays_ = true;
  z3::context& ctx_;
  int64_t unique_counter_;
  int64_t num_arrays_;

  // Uses name as the basis for the UF name. e is the concrete expression for
  // which you're creating a UF application.
  z3::expr AbstractUfIntParams(
      const std::string& name, const z3::expr& e,
      std::function<z3::expr(const z3::expr_vector&)> /*conc_decl*/);
  z3::sort AbstractSort(const z3::sort& s) const;
};

//^----------------------------------------------------------------------------^

//! Abstracts a concrete formula by rewriting away arrays using fresh Boolean
//! and bit vector variables that don't share contraints.  (1) Array equalities
//! are replaced with fresh Boolean variables.  (2) Array selects are replaced
//! with fresh bit vector variables.
class NukeArrays 
    : public ExprRewriter<NukeArrays>,
      public ExprVisitor<NukeArrays, z3::expr> {

 public:
  struct Stats {
    int64_t num_fresh_eqs = 0;
    int64_t num_fresh_selects = 0;
  };

  NukeArrays(z3::context& c) 
      : ctx_(c), unique_counter_(0) {}

  z3::expr operator()(const z3::expr& e) { return Rewrite(e); }
  z3::expr_vector operator()(const z3::expr_vector& es);

  z3::expr visitExpr(const z3::expr& e);
  z3::expr visitEQ(const z3::expr&);
  z3::expr visitSELECT(const z3::expr&);

  void collect_statistics(Statistics *st) const;

 private:
  z3::context& ctx_;
  int64_t unique_counter_;
  Stats stats_;
};

//^----------------------------------------------------------------------------^



//! This solver performs its own abstraction on concrete queries. The
//! abstraction is an attempt to solve simpler queries. Because the
//! abstraction over-approximates, if this solver returns SAT, the original
//! query may or may not be SAT. If this solver returns UNSAT, the original
//! query is also UNSAT.
class EufBvSolver : public Solver {
 public:
  virtual ~EufBvSolver() = default;

  // EufBvSolver (below) is written in terms of whatever this type is, so just
  // change it if you want to change the abstraction.
  using LayeredAbstraction = NukeArrays;

  struct Stats {
    int64_t num_checks = 0;

    void Reset() {
      (*this) = {};
    }
  };

  EufBvSolver(const std::shared_ptr<Solver>& s,
              const std::shared_ptr<LayeredAbstraction>& abs)
      : abstract_(abs), solver_(s) {}
  EufBvSolver(std::shared_ptr<Solver>&& s,
              const std::shared_ptr<LayeredAbstraction>& abs)
      : abstract_(abs), solver_(std::move(s)) {}

  std::unique_ptr<EufBvSolver> clone() const;
  
  virtual void Add(const z3::expr& e) override;

  virtual CheckResult Check(const size_t n,
                            const z3::expr* assumptions) override;
  using Solver::Check;

  virtual z3::expr_vector unsat_core() override;
  
  virtual std::shared_ptr<Model> get_model() override {
    throw new std::runtime_error("unimplemented");
  }
  
  virtual z3::expr_vector unsat_core_reasons() override {
    throw new std::runtime_error("unimplemented");
  }
  virtual z3::expr_vector assertions() const override {
    throw new std::runtime_error("unimplemented");
  }
  virtual std::string reason_unknown() const override {
    return "unknown reason";
  }
  virtual std::ostream& Print(std::ostream&) const override {
    throw new std::runtime_error("unimplemented");
  }

  virtual void DumpBenchmark(
      std::ostream& os, size_t n, const z3::expr* assumptions) override;
  using Solver::DumpBenchmark;
  
  virtual const char *version() const override {
    return "EufBvSolver";
  }

  void collect_statistics(Statistics *st) const override;

  //! Returns true if any abstraction so far has been vacuous
  bool is_concrete() const {
    return !found_non_spurious_abstraction_;
  }

 private:
  std::shared_ptr<LayeredAbstraction> abstract_;
  ExprMap<z3::expr> abs2orig_;
  std::shared_ptr<Solver> solver_;
  // initially all abstraction is spurious
  bool found_non_spurious_abstraction_ = false;
  Stats stats_;

  virtual inline z3::context& ctx() const override { return solver_->ctx(); }
  inline Solver& solver() const { return *solver_; }

  z3::expr Abstract(const z3::expr&);
};

} // end namespace euforia

#endif // EUFORIA_LAYERED_REFINEMENT_H_
