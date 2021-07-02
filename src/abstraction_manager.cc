// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include <numeric>
#include <sstream>

#include "abstraction_manager.h"
#include "supp/debug.h"
#include "supp/identity_rewriter.h"
#include "supp/std_supp.h" // GetWithDefault

using namespace std;

namespace euforia {

class Concretizer : public ExprRewriter<Concretizer>,
    public ExprVisitor<Concretizer, z3::expr> {
  const ConcreteFuncDeclMap& reverse_func_decls_;
  const ExprMap<z3::expr>& reverse_subst_;
 public:
  Concretizer(AbstractionManager& ar)
      : reverse_func_decls_(ar.reverse_func_decls_),
      reverse_subst_(ar.reverse_subst_) {}

  z3::expr visitExpr(const z3::expr& e) {
    z3::expr ret(e.ctx());
    auto args = NewArgsExprVector(e);
    // otherwise use the func_decl to create the concrete version
    auto declLoc = reverse_func_decls_.find(e.decl());
    if (declLoc != reverse_func_decls_.end()) {
      auto& concDecl = declLoc->second;
      ret = concDecl(args);
    } else if (auto entry = reverse_subst_.find(e); entry != reverse_subst_.end()) {
      ret = entry->second;
    } else {
      auto rw = make_identity_rewriter(args);
      ret = rw(e);
    }
    return ret;
  }

  //! abstract EQ may be false at concrete level, so handle
  z3::expr visitEQ(const z3::expr& e) {
    assert(e.num_args() == 2);
    auto a = Arg(e,0), b = Arg(e,1);
    if (a.is_bv() && b.is_bv()) {
      if (a.get_sort().bv_size() == b.get_sort().bv_size()) {
        return a == b;
      } else {
        return e.ctx().bool_val(false);
      }
    } else {
      return a == b;
    }
  }

  //! explode an abstract distinct node for some reason
  z3::expr visitDISTINCT(const z3::expr& e) {
    z3::expr_vector v(e.ctx());
    ExprVectorInserter conjoin(v);
    for (unsigned i = 0; i < e.num_args(); i++) {
      for (unsigned j = i+1; j < e.num_args(); j++) {
        auto a = Arg(e,i), b = Arg(e,j);

        if (a.is_bv() && b.is_bv()) {
          if (a.get_sort().bv_size() == b.get_sort().bv_size()) {
            *conjoin++ = (a != b);
          } else {
            // they are distinct, so, ignore
          }
        } else {
          *conjoin++ = !(a == b);
        }
      }
    }
    return expr_mk_and(v);
  }

};




/*----------------------------------------------------------------------------*/
/* abstract rewriter */

AbstractionManager::AbstractionManager(
    z3::context& c, const ExprMap<z3::expr>& ground) 
    : ctx_(c), concretizer_(make_unique<Concretizer>(*this)),
      abstract_arrays_(true) {
  for (auto& [concrete_var, abstract_var] : ground) {
    AddGroundAbstraction(concrete_var, abstract_var);
  }
}

AbstractionManager::~AbstractionManager() {}

void AbstractionManager::AddGroundAbstraction(const z3::expr& concrete_var,
                                              const z3::expr& abstract_var) {
  auto inserted = subst_.insert({concrete_var, abstract_var}).second;
  EUFORIA_ASSERT(inserted, "must be inserted, something very wrong");
  inserted = reverse_subst_.insert({abstract_var, concrete_var}).second;
  EUFORIA_ASSERT(inserted, "must be inserted, something very wrong");
  _unused(inserted);
}

z3::expr AbstractionManager::Abstract(const z3::expr& e) {
  auto e_abstract = Rewrite(e);
  return e_abstract;
}
    
  
AstMap<z3::expr_vector> AbstractionManager::GetConstsBySort() const {
  AstMap<z3::expr_vector> constsBySort;
  for (const z3::expr& c : constants_) {
    if (constsBySort.find(c.get_sort()) == constsBySort.end()) {
      constsBySort.emplace(c.get_sort(), z3::expr_vector(ctx_));
    }
    constsBySort.at(c.get_sort()).push_back(c);
  }
  return constsBySort;
}

// Returns an uninterpreted function/predicate based on given name and applies it to args
// Stores the decl in reverse_func_decls_
z3::expr AbstractionManager::AbstractUf(const std::string& name,
                                        const z3::expr& n,
                                        z3::sort sort,
                                        std::function<z3::expr(const z3::expr_vector&)> decl,
                                        const z3::expr_vector& args) {
  z3::sort_vector sorts(ctx_);
  z3::sort retSort = AbstractSort(sort);
  for (unsigned i = 0; i < args.size(); i++) {
    sorts.push_back(args[i].get_sort());
  }
  stringstream nameStream;
  nameStream << name;
  for (unsigned i = 0; i < args.size(); i++) {
    nameStream << "_" << SortName(n.arg(i).get_sort());
  }
  auto f = ctx_.function(nameStream.str().c_str(), sorts, retSort);
  /*auto newDecl =*/ reverse_func_decls_.insert({f, decl});
  return f(args);
}

z3::expr AbstractionManager::AbstractFresh(
    const std::string& name, z3::expr e) {
  // static int64_t fresh_index = 0;
  // logger.Log(6, "original term: {}", e);
  auto e_decl = e.decl();
  stringstream name_stream;
  name_stream << name;
  for (unsigned i = 0; i < e_decl.arity(); i++) {
    auto sort_name = SortName(e_decl.domain(i));
    name_stream << "_" << e.arg(i).decl().name();
    name_stream << "_" << sort_name;
  }
  name_stream << "_" << SortName(e_decl.range());
  // name_stream << "_" << ++fresh_index;
  
  auto ret_sort = AbstractSort(e_decl.range());
  z3::expr_vector args(e.ctx());
  z3::sort_vector sorts(e.ctx());
  auto f = e.ctx().function(name_stream.str().c_str(), sorts, ret_sort);
  // logger.Log(6, "f: {}", f);
  auto t = f(args);
  reverse_subst_.insert({t, e});
  // logger.Log(6, "new term: {}", t);
  return t;
}

// Uses name as the basis for the UF name. e is the concrete expression for
// which you're creating a UF application.
z3::expr AbstractionManager::AbstractUfIntParams(
    const std::string& name, const z3::expr& e,
    std::function<z3::expr(const z3::expr_vector&)> conc_decl) {
  // logger.Log(6, "original term: {}", e);
  auto e_decl = e.decl();
  stringstream name_stream;
  name_stream << name;
  for (unsigned i = 0; i < e_decl.arity(); i++) {
    auto sort_name = SortName(e_decl.domain(i));
    name_stream << "_" << sort_name;
  }
  name_stream << "_" << SortName(e_decl.range());

  z3::expr_vector args(e.ctx());
  z3::sort_vector sorts(e.ctx());
  auto ret_sort = AbstractSort(e_decl.range());
  // This code is specific to int parameters. If you have other types, you're
  // out of luck.
  auto num_parameters = Z3_get_decl_num_parameters(e.ctx(), e.decl());
  const int param_width = 32; // i decided this arbitrarily
  for (unsigned i = 0; i < num_parameters; i++) {
    auto p = Z3_get_decl_int_parameter(e.ctx(), e.decl(), i);
    auto p_bv = e.ctx().bv_val(p, param_width);
    auto p_abs = visitBNUM(p_bv);
    args.push_back(p_abs);
    sorts.push_back(AbstractSort(p_bv.get_sort()));
    logger.Log(6, "arg: {}, sort: {}", args[args.size()-1],
               sorts[sorts.size()-1]);
  }
  for (unsigned i = 0; i < e_decl.arity(); i++) {
    args.push_back(Arg(e, i));
    sorts.push_back(Arg(e, i).get_sort());
    // logger.Log(6, "arg: {}, sort: {}", args[args.size()-1],
    //            sorts[sorts.size()-1]);
  }
  // logger.Log(6, "ret_sort: {}", ret_sort);

  auto f = e.ctx().function(name_stream.str().c_str(), sorts, ret_sort);
  // logger.Log(6, "f: {}", f);
  reverse_func_decls_.insert({f, conc_decl});
  auto term = f(args);
  // logger.Log(6, "new term: {}", term);
  return term;
}
                                      


z3::sort AbstractionManager::AbstractSort(const z3::sort& s) const {
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
    return s.ctx().uninterpreted_sort((uninterpreted_bv_sort_name + to_string(s.bv_size())).c_str());
  }
}


// by default, rewrite expr by calling the decl() on its rewritten arguments
z3::expr AbstractionManager::visitExpr(const z3::expr& e) {
  z3::expr ret(e.ctx());
  switch (e.decl().decl_kind()) {
    case Z3_OP_NOT:
      ret = expr_not(Arg(e,0));
      break;

    case Z3_OP_OR:
      ret = expr_mk_or(e.ctx(), args(e));
      break;

    case Z3_OP_AND:
      ret = expr_mk_and(e.ctx(), args(e));
      break;

    default: {
      auto rw = make_identity_rewriter(NewArgsExprVector(e));
      ret = rw(e);
    }
  }

  return ret;
}

/// ====== visitor overrides
z3::expr AbstractionManager::visitUNINTERPRETED(const z3::expr& n) {
  if (auto search = subst_.find(n); search != subst_.end()) {
    return search->second;
  }

  z3::sort_vector sorts(ctx_);
  if (n.num_args() == 0) {
    z3::expr ret = n;
    if (n.is_array() && !abstract_arrays_) {
      // replace with term->term array
      ret =  ctx_.constant(("^" + n.decl().name().str()).c_str(), AbstractSort(n.get_sort()));
    } else if (!n.is_bool()) {
      ret = ctx_.constant(("^" + n.decl().name().str()).c_str(), AbstractSort(n.get_sort()));
    }
    if (!z3::eq(n, ret)) {
      AddGroundAbstraction(n, ret);
    }
    return ret;
  } else {
    z3::expr_vector args(n.ctx());
    for (unsigned i = 0; i < n.num_args(); i++) {
      args.push_back(Arg(n, i));
    }
    return AbstractUf(n.decl().name().str(), n, n.get_sort(), n.decl(), args);
  }
}


z3::expr AbstractionManager::visitDISTINCT(const z3::expr& e) {
  z3::expr_vector args(e.ctx());
  for (unsigned i = 0; i < e.num_args(); i++)
    args.push_back(Arg(e, i));
  return expr_distinct(args).simplify();
}

z3::expr AbstractionManager::visitSGT(const z3::expr& e) {
  auto concDecl = [](const z3::expr_vector& args) -> z3::expr {
    assert(args.size()==2);
    return args[0] > args[1];
  };
  return AbstractUf("SGT", e, e.get_sort(), concDecl, NewArgsExprVector(e));
}

z3::expr AbstractionManager::visitUGT(const z3::expr& e) {
  auto concDecl = [](const z3::expr_vector& args) -> z3::expr {
    assert(args.size()==2);
    return z3::ugt(args[0], args[1]);
  };
  return AbstractUf("UGT", e, e.get_sort(), concDecl, NewArgsExprVector(e));
}


z3::expr AbstractionManager::visitBNUM(const z3::expr& n) {
  string numstr;
  auto b = n.is_numeral(numstr);
  assert(b);
  _unused(b);
  auto name = ("$K" + to_string(n.get_sort().bv_size()) + "_" + numstr);
  auto numSort = AbstractSort(n.get_sort());
  auto ret = ctx_.constant(name.c_str(), numSort);
  reverse_func_decls_.insert({ret.decl(), n.decl()});
  const auto& entry = constants_.insert(ret);
  dirty_ |= entry.second;
  static int break_count = 0;
  if (entry.second) {
    ++break_count;
  }
  return ret;
}

// Each EXTRACT has hi and log parameters plus one argument of a given type to
// apply it to. This function returns a UF like EXTRACT_<TYPE>_<RET-TYPE> : U8
// -> U8
z3::expr AbstractionManager::visitEXTRACT(const z3::expr& e) {
  // extract in z3 uses "parameters" not "arguments" to specify the hi and lo for extracting
  auto conc_decl = [](const z3::expr_vector& args) -> z3::expr {
    unsigned hi, lo;
    auto b = Z3_get_numeral_uint(args.ctx(), args[0], &hi);
    _unused(b);
    assert(b);
    b = Z3_get_numeral_uint(args.ctx(), args[1], &lo);
    assert(b);
    return z3::to_expr(args.ctx(), Z3_mk_extract(args.ctx(), hi, lo, args[2]));
  };
  return AbstractUfIntParams("EXTRACT", e, conc_decl);
}

z3::expr AbstractionManager::visitCONCAT(const z3::expr& e) {
  assert(e.num_args() == 2);
  z3::expr_vector args(e.ctx());
  for (unsigned i = 0; i < e.num_args(); i++) {
    args.push_back(Arg(e,i));
  }
  auto concDecl = [](const z3::expr_vector& args) -> z3::expr { assert(args.size() == 2); return z3::concat(args); };
  return AbstractUf("CONCAT", e, e.get_sort(), concDecl, args);
}

z3::expr AbstractionManager::visitSIGN_EXT(const z3::expr& e) {
  auto conc_decl = [](const z3::expr_vector& args) -> z3::expr {
    int added_bits;
    auto b = Z3_get_numeral_int(args.ctx(), args[0], &added_bits);
    assert(b);
    _unused(b);
    return z3::to_expr(args.ctx(), Z3_mk_sign_ext(args.ctx(), added_bits,
                                                  args[1]));
  };
  return AbstractUfIntParams("SIGN_EXT", e, conc_decl);
}


z3::expr AbstractionManager::visitZERO_EXT(const z3::expr& e) {
  auto conc_decl = [](const z3::expr_vector& args) -> z3::expr {
    int added_bits;
    auto b = Z3_get_numeral_int(args.ctx(), args[0], &added_bits);
    assert(b);
    _unused(b);
    return z3::to_expr(args.ctx(), Z3_mk_zero_ext(args.ctx(), added_bits,
                                                  args[1]));
  };
  return AbstractUfIntParams("ZERO_EXT", e, conc_decl);
}


z3::expr AbstractionManager::visitSTORE(const z3::expr& e) {
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
    reverse_func_decls_.insert({ret.decl(), e.decl()});
    return ret;
  }
}

z3::expr AbstractionManager::visitSELECT(const z3::expr& e) {
  assert(e.num_args()==2);
  if (abstract_arrays_) {
    std::function<z3::expr(const z3::expr_vector&)> decl =
        [](const z3::expr_vector& args) {
          assert(args.size() == 2);
          return z3::select(args[0], args[1]);
        };
    if (abstract_array_select_fresh_) {
      // abstracts select(a, i) as fresh term SELECT_a_i (0-arity term)
      return AbstractFresh("SELECT", e);
    } else {
      return AbstractUfIntParams("SELECT", e, decl);
    }
  } else {
    return z3::select(Arg(e,0), Arg(e,1));
  }
}

z3::expr AbstractionManager::visitCONST_ARRAY(const z3::expr& e) {
  auto sort = e.get_sort().array_domain();
  std::function<z3::expr(const z3::expr_vector&)> decl =
      [=](const z3::expr_vector& args) {
        if (abstract_arrays_) {
          assert(args.size() == 2);
          return z3::const_array(sort, args[1]);
        } else {
          return z3::const_array(sort, args[0]);
        }
      };
  if (abstract_arrays_) {
    return AbstractUfIntParams("CONST-ARRAY", e, decl);
  } else {
    auto abs = 
        z3::const_array(AbstractSort(e.get_sort().array_domain()), Arg(e,0));
    reverse_func_decls_.insert({abs.decl(), decl});
    return abs;
  }
}

//^----------------------------------------------------------------------------^
//concretization

z3::expr AbstractionManager::Concretize(const z3::expr& e) {
  auto r = concretizer_->Rewrite(e);
  return r;
}

}
