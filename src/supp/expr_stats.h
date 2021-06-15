// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef expr_stats_hpp
#define expr_stats_hpp

#include "checker_types.h"
#include "supp/expr_visitor.h"
#include "supp/expr_iterators.h"



namespace euforia {
  struct ExprStats : public ExprVisitor<ExprStats> {
    ExprMap<unsigned> eocc;
    AstMap<unsigned> docc;
    AstMap<unsigned> focc;
    int64_t num_arrays = 0;

    ExprStats() {}

    void operator()(const z3::expr& e) {
      traverse(e);
    }

    void traverse(const z3::expr& e) {
      for (auto I = df_expr_iterator::begin(e), E = df_expr_iterator::end(e); I != E; ++I) {
        visit(*I);
      }
    }
    
    void visitExpr(const z3::expr& e) {
      eocc[e]++;
      docc[e.decl()]++;
      if (e.decl().arity() > 0)
        focc[e.decl()]++;
      if (e.get_sort().is_array()) {
        num_arrays++;
      }
    }
  };
  
  std::ostream& operator<<(std::ostream& os, const ExprStats& stats);
}
#endif
