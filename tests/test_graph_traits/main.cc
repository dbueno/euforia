// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "checker_types.h"
#include "supp/expr_iterators.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_supp.h"
#include "supp/model_justifier.h"
#include "supp/tseitin_rewriter.h"
#include "xsys/model_pruning_sets.h"

using namespace euforia;
using namespace std;

int main(int, char **) {
  logger.set_level(1);
  z3::context c;
  auto ctx = [&]() -> z3::context& { return c; };
  auto make_var = [&](auto&& name, auto&& sort) {
    return make_pair(ctx().constant(name, sort),
                     ctx().constant((string(name) + "+").c_str(), sort));
  };

  auto [x, x_next] = make_var("x", ctx().bv_sort(8));
  auto [y, y_next] = make_var("y", ctx().bv_sort(8));
  (void)y;
  auto [z, z_next] = make_var("z", ctx().bv_sort(8));

  auto f = x_next == (x + 1) && z_next == z;
  f = f || (y_next == (x + 1) && z_next == z);

  fmt::print("legend\n");
  for (auto it = po_expr_iterator::begin(f),
       ie = po_expr_iterator::end(f); it != ie; ++it) {
    fmt::print("{:8x}: {}\n", (*it).hash(), *it);
  }
  fmt::print("\n");

  {
    z3::solver s(ctx()); 
    s.add(f);
    auto result = s.check();

    if (result == z3::check_result::sat) {
      auto m = s.get_model();
      auto eval = [&](auto&& e, bool c = false) { return m.eval(e, c); } ;
      ModelPruningTraversal mp(eval);

      fmt::print("pruned nodes (should be all nodes on one side of the or)\n");
      for (auto it = mp.begin(f), ie = mp.end(f); it != ie; ++it) {
        for(auto& elt : ExprConjuncts(*it)) {
          fmt::print("{:8x} {}\n", (elt).hash(), eval(elt));
          fmt::print("--------------\n");
          std::flush(std::cout);
        }
      }

      fmt::print("predicates (should be only 2)\n");
      ExprSet predicates;
      ModelJustifier justify(eval);
      auto terms = {f};
      justify.ComputePredicates(begin(terms), end(terms), &predicates);
      for (auto& pred : predicates) {
        fmt::print("{:8x} {}\n", pred.hash(), eval(pred));
      }
    }
  }

  
#if 0
  fmt::print("\ntseitin rewriting test\n");
  int fresh_count = 0;
  auto fresh_var = [&](const char *prefix) {
    string name(prefix);
    name += to_string(++fresh_count);
    return ctx().bool_const(name.c_str());
  };
  TseitinRewriter tseitin(ctx(), fresh_var);
  tseitin(f);
  auto defs = tseitin.TakeDefs();
  {
    fmt::print("legend\n");
    for (auto& f : tseitin.clauses()) {
      for (auto it = po_expr_iterator::begin(f),
           ie = po_expr_iterator::end(f); it != ie; ++it) {
        fmt::print("{:8x}: {}\n", (*it).hash(), *it);
      }
    }
    fmt::print("\n");
    z3::solver s(ctx());
    for (auto& c : tseitin.clauses()) {
      s.add(c);
    }
    auto result = s.check();


    if (result == z3::check_result::sat) {
      auto m = s.get_model();
      fmt::print("{}\n", m);
      int num_evals = 0;
      auto eval = [&](auto&& e, bool c) {
        ++num_evals;
        if (auto search = defs->right.find(e); search != defs->right.end()) {
          logger.Log(1, "calling eval on {} instead of {}", search->second, e);
          return m.eval(search->second, c);
        }
        logger.Log(1, "calling eval on {}", e);
        // EUFORIA_DEBUG_BREAK;
        return m.eval(e, c);
      };
      ModelPruningTraversal mp(eval, defs.get());

      fmt::print("pruned nodes (should be all nodes on one side of the or)\n");
      auto& f = tseitin.clauses().back();
      for (auto it = mp.begin(f), ie = mp.end(f); it != ie; ++it) {
        for(auto& elt : ExprConjuncts(*it)) {
          fmt::print("{:8x} {}\n", (elt).hash(), m.eval(elt));
          fmt::print("--------------\n");
          std::flush(std::cout);
        }
      }
      
      fmt::print("predicates (should be only 2)\n");
      ExprSet predicates;
      ModelJustifier justify(eval, defs.get(), &predicates);
      auto terms = {f};
      justify.ComputePredicates(begin(terms), end(terms));
      for (auto& pred : predicates) {
        fmt::print("{:8x} {}\n", pred.hash(), m.eval(pred));
      }

      fmt::print("{} evals\n", num_evals);
    }
  }
#endif
}
