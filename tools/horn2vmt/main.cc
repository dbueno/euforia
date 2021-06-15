// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

// Represented by HornTransStateSpace: What is common to all the sliced
// transition relations? The state variables of the transition system; the rule
// activation vars.
//
// Represented by HornSetTrans: What is different between the sliced transition
// relations? The transition relation itself. The inputs derived from the
// quantified vars. The inputs for the commander vars. The cones.


#define BOOST_RESULT_OF_USE_DECLTYPE

#include <boost/algorithm/cxx11/all_of.hpp>
#include <boost/range/algorithm/transform.hpp>
#include <boost/range/algorithm/copy.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/optional.hpp>
#include <boost/program_options.hpp>
#include <boost/range.hpp>
#include <boost/range/adaptor/indexed.hpp>
#include <boost/range/combine.hpp>
#include <fstream>
#include <gmpxx.h>
#include <map>
#include <set>
#include <sstream>
#include <vector>
#include <z3++.h>

#include "checker_types.h"
#include "supp/expr_flattener.h"
#include "supp/expr_iterators.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_substitution.h"
#include "supp/expr_supp.h"
#include "supp/nnf_rewriter.h"
#include "xsys/state_vars.h"
#include "xsys/vmt_transition_system.h"
#include "one_hot.h"

using namespace std;
using namespace euforia;

using euforia::vmt::VmtTransitionSystem;

namespace {
struct Config {
  string input_filename;
  bool allocate_vars_by_sort = false;
  bool allocate_inputs_by_sort = true;
  boost::optional<string> varmap_filename;
  bool slice_t = false;
  bool enable_one_hots = true;
};

Config config;

class Int2BvRewriter : public ExprRewriter<Int2BvRewriter>,
    public ExprVisitor<Int2BvRewriter, z3::expr> {
 public:
  Int2BvRewriter(z3::context& c, int bv_width) : bv_sort_(c.bv_sort(bv_width)) {}

  z3::expr operator()(const z3::expr& e) { return Rewrite(e); }

  z3::sort TranslateSort(const z3::sort& s) {
    switch (s.sort_kind()) {
      case Z3_INT_SORT:
        return bv_sort_;
      case Z3_ARRAY_SORT:
        return ctx().array_sort(TranslateSort(s.array_domain()),
                                TranslateSort(s.array_range()));
      default:
        return s;
    }
  }

  z3::expr visitExpr(const z3::expr& e) {
    return e.decl()(NewArgsExprVector(e));
  }

  z3::expr visitQUANTIFIER(const z3::expr& e) {
    z3::expr e_new(e.ctx());
    vector<Z3_sort> var_sorts;
    vector<Z3_symbol> var_names;
    for (unsigned i = 0; i < Z3_get_quantifier_num_bound(e.ctx(), e); i++) {
      z3::sort var_sort(e.ctx(), Z3_get_quantifier_bound_sort(e.ctx(), e, i));
      var_sorts.push_back(TranslateSort(var_sort));
      var_names.push_back(Z3_get_quantifier_bound_name(e.ctx(), e, i));
    }
    if (e.is_forall()) {
      Z3_pattern pats[0];
      e_new = z3::to_expr(
          e.ctx(),
          Z3_mk_forall(e.ctx(), 0, 0, pats, var_sorts.size(),
                       var_sorts.data(), var_names.data(), lookup(e.body())));
    } else if (e.is_exists()) {
      Z3_pattern pats[0];
      e_new = z3::to_expr(
          e.ctx(),
          Z3_mk_exists(e.ctx(), 0, 0, pats, var_sorts.size(),
                       var_sorts.data(), var_names.data(), lookup(e.body())));
    } else {
      EUFORIA_FATAL("unknown quantifier");
    }
    // logger.Log(0, "{}:{}", e, e.get_sort());
    // logger.Log(0, "{}:{}", e_new, e_new.get_sort());
    return e_new;
  }

  z3::expr visitVAR(const z3::expr& e) {
    auto ret = z3::to_expr(
        e.ctx(),
        Z3_mk_bound(e.ctx(), Z3_get_index_value(e.ctx(), e),
                    TranslateSort(e.get_sort())));
    return ret;
  }

  z3::expr visitANUM(const z3::expr& e) {
    string decimal_str;
    z3::expr bv(e.ctx());
    if (!e.is_numeral(decimal_str)) {
      EUFORIA_FATAL("not a numeral: {}", e);
    }
    logger.Log(4, "found numeral: {}", decimal_str);
    mpz_class num(decimal_str);
    string binstr = num.get_str(2);
    logger.Log(4, "    binary: {}", binstr);
    // create bits, which has num but padded with zeros
    string bits(bv_sort_.bv_size(), '0');
    int width = static_cast<int>(bv_sort_.bv_size());
    // binstr will be bits if num is positive, and -bits if num is negative
    if (binstr[0] != '-') {
      assert(binstr.size() > 0);
      assert(binstr.size() <= bv_sort_.bv_size());
      copy(binstr.begin(), binstr.end(),
           bits.begin() + (bits.size() - binstr.size()));
      bool bool_bits[width];
      // bits is in reverse order from what z3 expects; z3 wants LSB first
      for (int i = 0, j = width-1; i < width; i++, j--) {
        bool_bits[j] = bits[i] == '0' ? false : true;
      }
      bv = ctx().bv_val(width, bool_bits);
      logger.Log(4, "    binary padded: {}", bits);
    } else {
      assert(binstr.size() > 1);
      // create bits, which has num but padded with zeros
      copy(next(binstr.begin()), binstr.end(),
           next(bits.begin()) + (bits.size() - binstr.size()));
      logger.Log(4, "    binary uminus: {}", bits);
      bool bool_bits[width];
      // bits is in reverse order from what z3 expects; z3 wants LSB first
      for (int i = 0, j = width-1; i < width; i++, j--) {
        bool_bits[j] = bits[i] == '0' ? false : true;
      }
      bv = ctx().bv_val(width, bool_bits);
      // constant 1 bits
      for (int i = 0; i < width; i++) {
        bool_bits[i] = true;
      }
      auto all_ones = ctx().bv_val(width, bool_bits);
      // flip all the bits and add one: 2's complement representation 
      bv = bv ^ all_ones;
      bv = bv + 1;
      bv = bv.simplify();
    }
    logger.Log(4, "    bv result: {}", bv);
    return bv;
  }

  z3::expr visitUNINTERPRETED(const z3::expr& e) {
    assert(!e.is_array());
    // Create an uninterpreted function that takes BVs instead of Ints
    auto e_decl = e.decl();
    vector<z3::sort> f_sorts;
    for (unsigned i = 0; i < e_decl.arity(); i++) {
      f_sorts.push_back(TranslateSort(e_decl.domain(i)));
    }
    auto f_decl = e.ctx().function(
        e_decl.name(), e_decl.arity(), f_sorts.data(),
        TranslateSort(e_decl.range()));
    return f_decl(NewArgsExprVector(e));
  }

  z3::expr visitSELECT(const z3::expr& e) {
    logger.Log(4, "select {}", e);
    for (auto&& arg : boost::make_iterator_range(args_begin(e), args_end(e))) {
      logger.Log(4, "    rewritten args {}:{}", arg, arg.get_sort());
    }
    return z3::select(arg(e,0), arg(e,1));
  }

  z3::expr visitSTORE(const z3::expr& e) {
    return z3::store(arg(e,0), arg(e,1), arg(e,2));
  }

  z3::expr visitEQ(const z3::expr& e) {
    return arg(e,0) == arg(e,1);
  }

  z3::expr visitADD(const z3::expr& e) {
    z3::expr ret(e.ctx());
    for (auto&& arg : boost::make_iterator_range(args_begin(e), args_end(e))) {
      ret = bool(ret) ? ret + arg : arg;
    }
    return ret;
  }

  z3::expr visitSUB(const z3::expr& e) {
    assert(e.num_args() == 2);
    return arg(e,0) - arg(e,1);
  }

  z3::expr visitUMINUS(const z3::expr& e) {
    return -arg(e,0);
  }

  z3::expr visitMUL(const z3::expr& e) {
    assert(e.num_args() == 2);
    return arg(e,0) * arg(e,1);
  }

  z3::expr visitDIV(const z3::expr& e) {
    return arg(e,0) / arg(e,1); // signed division
  }

  z3::expr visitIDIV(const z3::expr& e) {
    return arg(e,0) / arg(e,1);
  }

  z3::expr visitREM(const z3::expr& e) {
    return z3::srem(arg(e,0), arg(e,1));
  }

  z3::expr visitMOD(const z3::expr& e) {
    return z3::smod(arg(e,0), arg(e,1));
  }

  z3::expr visitLE(const z3::expr& e) {
    return arg(e,0) <= arg(e,1);
  }

  z3::expr visitLT(const z3::expr& e) {
    return arg(e,0) < arg(e,1);
  }

  z3::expr visitGE(const z3::expr& e) {
    return arg(e,0) >= arg(e,1);
  }

  z3::expr visitGT(const z3::expr& e) {
    return arg(e,0) > arg(e,1);
  }

  z3::context& ctx() const { return bv_sort_.ctx(); }

 private:
  z3::sort bv_sort_;
};

//^----------------------------------------------------------------------------^
//

class HornRule {
 public:
  HornRule(const z3::expr& rule, int index) 
      : head_(rule.ctx()), body_(rule.ctx()), rule_(rule), index_(index) {
    auto b = rule;
    if (rule.is_quantifier()) {
      b = rule.body();
    } else if (is_not(rule) && rule.arg(0).is_quantifier()) {
      b = rule.arg(0).body();
    }
    body_ = ctx().bool_val(true);
    if (b.is_implies()) {
      head_ = b.arg(1);
      body_ = b.arg(0);
    } else {
      head_ = b;
    }
  }

  bool is_linear() const {
    IterExprSet visited;
    int relation_count =
        count_if(df_expr_ext_iterator::begin(body(), visited),
                 df_expr_ext_iterator::end(body(), visited),
                 [&](auto&& x) { return x.is_app() &&
                     x.decl().decl_kind() == Z3_OP_UNINTERPRETED; });
    // int relation_count =
    //     count_if(df_expr_iterator::begin(rule.body()),
    //              df_expr_iterator::end(rule.body()),
    //              [&](auto&& x) { return x.is_app() &&
    //                  relation_vars_.find(x.decl()) != relation_vars_.end(); });
    if (relation_count > 1) {
      return false;
      // throw std::runtime_error("nonlinear Horn clause detected, exiting");
    }
    return true;
  }

  bool is_query() const {
    if (is_literal_false(head())) {
      return true;
    }
   if (is_not(head()) &&
       head().arg(0).decl().decl_kind() == Z3_OP_UNINTERPRETED) {
     return true;
   }
   return false;
  }

  int index() const { return index_; }
  z3::context& ctx() const { return head_.ctx(); }
  z3::expr head() const { return head_; }
  z3::expr body() const { return body_; }
  operator z3::expr() const { return rule_; }
  std::string head_name() const {
    return head_.decl().name().str();
  }

 private:
  z3::expr head_;
  z3::expr body_;
  z3::expr rule_;
  int index_;
};

std::ostream& operator<<(std::ostream& os, const HornRule& r) {
  fmt::print(os, "HornRule: head {} body:\n{}", r.head(), r.body());
  return os;
}

//^----------------------------------------------------------------------------^
//

//! Groups a set of Horn clauses all of which have the same head symbol. The
//! head symbol is determined by the first rule added to the group.
class HornTransition {
 public:
  HornTransition() {}

  void AddRule(const HornRule& r, int i) {
    if (head_name_) {
      if (r.head_name() != head_name()) {
        throw std::runtime_error(
            fmt::format("adding bad rule to {} group: {}", *head_name_, r));
      }
    } else {
      head_name_ = r.head_name();
    }
    rules_.push_back({r,i});
  }

  const std::string& head_name() const { return *head_name_; }
  const std::vector<HornRule>& rules() const { return rules_; }

 private:
  boost::optional<std::string> head_name_;
  std::vector<HornRule> rules_;
};

//^----------------------------------------------------------------------------^
//

// Represents a complete set of Horn clauses -- a model checking instance -- as
// a collection of rules. Supports parsing both SMT2-style and
// declare-rel-style Horn clauses, thanks to z3.
class HornClauses {
 public:
  HornClauses(z3::context& c, const char *filename, bool int2bv = false) 
      : ctx_(c) {

    // Reads file into buffer because we may need to parse twice
    std::ifstream fin(filename);
    std::stringstream sstr;
    sstr << fin.rdbuf();
    auto filebuf = sstr.str();

    // Parses as declare-rel at first
    z3::fixedpoint fp(ctx());
    auto vec = Z3_fixedpoint_from_string(c, fp, filebuf.c_str());
    if (!vec) {
      fmt::print(cerr, "Parse error: {}", filename);
      exit(1);
    }
    auto queries = z3::ast_vector_tpl<z3::expr>(c, vec);
    z3::expr_vector rules(c);
    rules = fp.rules();
    
    if (queries.size() > 0) {
      assert(queries[0].num_args() == 0);
      rules.push_back(z3::implies(queries[0], ctx().bool_val(false)));
    }

    if (rules.empty()) {
      logger.Log(2, "0 fp rules found, so parsing as smtlib2");
      // Parses again as SMTLIB-2 HORN file
      rules = ctx().parse_string(filebuf.c_str());
    }
    logger.Log(1, "parsed {} rules", rules.size());
    if (int2bv) {
      Int2BvRewriter rewrite_int2bv(ctx(), 32);
      for (unsigned i = 0; i < rules.size(); i++) {
        auto r = rewrite_int2bv(rules[i]);
        rules.set(i, r);
      }
    }
    rules_.reserve(rules.size());
    for (unsigned i = 0; i < rules.size(); i++) {
      rules_.push_back(HornRule(rules[i], i));
    }
  }

  z3::context& ctx() const { return ctx_; }

  // Iterates over the database as HornRules
  auto rules() const {
    return boost::make_iterator_range(rules_.begin(), rules_.end());
  }

  FuncDeclMap<HornTransition> group_by_heads() const {
    using namespace boost::adaptors; // indexed
    // Groups horn rules by head symbol
    FuncDeclMap<HornTransition> head2trans;
    for (const auto& indexed_rule : rules() | indexed(0)) {
      const auto& index = indexed_rule.index();
      const auto& rule = indexed_rule.value();
      head2trans[rule.head().decl()].AddRule(rule, index);
    }
    return head2trans;
  }

  size_t size() const { return rules_.size(); }
 
 private:
  z3::context& ctx_;
  // Contains all the rules plus the query written as a rule (false => head)
  std::vector<HornRule> rules_;
};

//^----------------------------------------------------------------------------^
//

using RelationVarMap = FuncDeclMap<z3::expr>;
using PlaceVarsMap = FuncDeclMap<vector<z3::expr>>;

static string SortName(const z3::sort& sort) {
  if (sort.is_bv()) {
    return fmt::format("bv{}", sort.bv_size());
  } else if (sort.is_bool()) {
    return "bool";
  } else if (sort.is_array()) {
    auto domain_name = SortName(sort.array_domain());
    auto range_name = SortName(sort.array_range());
    return fmt::format("arr-{}-{}", domain_name, range_name);
  } else {
    fmt::print("{}\n", sort);
    EUFORIA_FATAL("unhandled sort");
  }
}


//! Represents the state space for translating a set of Horn clauses. Creates
//! relation variables, place variables, and rule activation inputs. All such
//! objects are created in the current output transition system, set in the
//! constructor and via set_output_xsys.
//!
//! This can be used to represent the state space for an entire set of clauses.
//! But it also has the flexibility of representing the state space for a
//! subset of clauses.
class HornTransStateSpace {
 public:
  HornTransStateSpace() : xsys_(nullptr) {}
  HornTransStateSpace(Config& cfg, const std::vector<HornRule>& rules,
                      VmtTransitionSystem *xsys) 
      : xsys_(xsys) {
    SortMap<std::vector<z3::expr>> relation_places_by_sort;
    for (const auto& rule : rules) {
      logger.Log(3, "creating state space for rule: {} => {}", rule.body(),
                 rule.head());
      // Creates rule activation variables
      auto rule_activation_input =
          ctx().bool_const(("r-" + to_string(rule.index())).c_str());
      auto& rule_activation = xsys_->AddInput(MakeInput(rule_activation_input));
      activation_input_vars_.push_back(rule_activation);
      // Pick up relations from rule heads; then declare Boolean relation vars
      // and place vars for each place. 
      if (auto decl = rule.head().decl();
          decl.decl_kind() == Z3_OP_UNINTERPRETED) {
        // Create r elation var
        auto relation_name = decl.name().str();
        auto var_name = "at-" + relation_name;
        if (xsys_->FindVar(var_name)) { // Skips present variables.
          continue;
        }
        auto& var = xsys_->AddVar(MakeStateVar(
                ctx().bool_const(var_name.c_str()),
                ctx().bool_const((var_name + "+").c_str())));
        relation_vars_.insert({decl, var.current()});
        // Ensures vector is initialized for all relations, even nullary ones
        (void)place_vars_[decl];
        // Open varmap file, if we need to
        ofstream varmap_out;
        if (cfg.varmap_filename) {
          varmap_out = ofstream(*cfg.varmap_filename);
          if (!varmap_out) {
            fmt::print(cerr, "warning: could not open varmap file: {}:\n{}\n",
                       *cfg.varmap_filename, strerror(errno));
            cfg.varmap_filename = boost::none;
          }
        }
        if (cfg.allocate_vars_by_sort) {
          SortMap<int> counts;
          for (unsigned i = 0; i < decl.arity(); i++) {
            if (counts.find(decl.domain(i)) == counts.end()) {
              counts[decl.domain(i)] = 0;
            }
            counts[decl.domain(i)] += 1;
          }
          for (auto&& [sort, num_occurrences] : counts) {
            int num_places =
                static_cast<int>(relation_places_by_sort[sort].size());
            for (int i = 0; i < (num_occurrences - num_places); i++) {
              auto name =
                  (SortName(sort) + "-place-" + to_string(num_places+i));
              auto& place_var = xsys_->AddVar(MakeStateVar(
                      ctx().constant(name.c_str(), sort),
                      ctx().constant((name + "+").c_str(), sort)));
              relation_places_by_sort[sort].push_back(place_var.current());
            }
          }
          counts.clear();
          for (unsigned i = 0; i < decl.arity(); i++) {
            auto place_var = relation_places_by_sort.at(
                decl.domain(i))[counts[decl.domain(i)]];
            if (varmap_out) {
              fmt::print(varmap_out, "Relation {} place {} mapped to var {}\n",
                         relation_name, i, place_var);
            }
            // EUFORIA_DEBUG_BREAK;
            place_vars_[decl].push_back(place_var);
            counts[decl.domain(i)]++;
          }
        } else {
          // allocate vars by relation
          for (unsigned i = 0; i < decl.arity(); i++) {
            auto place_name = relation_name + "-place-" + to_string(i);
            auto& place_var = xsys_->AddVar(MakeStateVar(
                    ctx().constant(place_name.c_str(), decl.domain(i)),
                    ctx().constant((place_name + "+").c_str(),
                                   decl.domain(i))));
            if (varmap_out) {
              fmt::print(varmap_out, "Relation {} place {} mapped to var {}\n",
                         relation_name, i, place_var.current());
            }
            place_vars_[decl].push_back(place_var.current());
          }
        }
      }
    }
    logger.Log(3, "created {} state variables", xsys_->num_vars());
    if (logger.ShouldLog(4)) {
      for (auto&& v : xsys_->vars()) {
        logger.Log(4, "  {}", v.current());
      }
    }
    logger.Log(3, "created {} inputs", xsys_->num_inputs());
  }

  const StateVar& get_head_relation_var(const HornRule& r) const {
    auto& v_expr = relation_vars_.at(r.head().decl());
    return *xsys_->FindVar(v_expr);
  } 

  const PrimaryInput& get_activation_var(const HornRule& r) const {
    auto& i_expr = activation_input_vars_.at(r.index());
    return *xsys_->FindInput(i_expr);
  }

  auto iter_place_vars(const z3::expr& e) const {
    class GetVar {
     public:
      GetVar(const VmtTransitionSystem& xsys) : xsys_(xsys) {}
      const StateVar& operator()(const z3::expr& var) const {
        return *xsys_.FindVar(var);
      }
     private:
      const VmtTransitionSystem& xsys_;
    };
    const auto& place_var_vec = place_vars_.at(e.decl());
    return boost::make_iterator_range(
        boost::make_transform_iterator(begin(place_var_vec),
                                       GetVar(*xsys_)),
        boost::make_transform_iterator(end(place_var_vec),
                                       GetVar(*xsys_)));
  }

  //! Iterates over the place variables for the relation in r's head
  auto iter_head_place_vars(const HornRule& r) const {
    return iter_place_vars(r.head());
  }

  //! Iterates over the Boolean relation vars in the transition system
  auto relation_vars() const {
    class GetVar {
     public:
      GetVar(const VmtTransitionSystem& xsys) : xsys_(xsys) {}
      const StateVar& operator()(const RelationVarMap::value_type& p) const {
        return *xsys_.FindVar(p.second);
      }
      const VmtTransitionSystem& xsys_;
    };
    return boost::make_iterator_range(
        boost::make_transform_iterator(relation_vars_.begin(), GetVar(*xsys_)),
        boost::make_transform_iterator(relation_vars_.end(), GetVar(*xsys_)));
  }

  auto activation_input_vars_begin() const {
    return activation_input_vars_.cbegin();
  }

  auto activation_input_vars_end() const {
    return activation_input_vars_.cend();
  }

  //! Returns zipped iterator over [ <e-arg-0, place-var-0>, <e-arg-1,
  //! place-var-1>, ... ]. Precondition: e must be an unintpreted Horn relation
  //! symbol.
  auto iter_args_with_places(const z3::expr& e) const {
    assert(e.num_args() == place_vars_.at(e.decl()).size());
    return boost::combine(ExprArgs(e), iter_place_vars(e));
  }

  //! Finds Boolean relation var for uninterpreted application e
  boost::optional<z3::expr> find_relation_var(const z3::expr& e) const {
    if (auto search = relation_vars_.find(e.decl());
        search != relation_vars_.end()) {
      return search->second;
    }
    return boost::none;
  }

  z3::context& ctx() const { return xsys_->ctx(); }
  VmtTransitionSystem& xsys() const { return *xsys_; }
  size_t num_relations() const { return relation_vars_.size(); }

  void set_output_xsys(VmtTransitionSystem *xsys) { xsys_ = xsys; }
 
 private:
  // output to
  VmtTransitionSystem *xsys_;
  // Maps func_decl to Boolean state var
  RelationVarMap relation_vars_;
  // List of Boolean state vars
  std::vector<z3::expr> activation_input_vars_;
  // Maps func_decl to list of place state vars
  PlaceVarsMap place_vars_;
};

//^----------------------------------------------------------------------------^
//
//! Helper for rewriting the bodies of Horn clauses in terms of relation vars
//! and place vars
class Horn2VmtRewriter : public ExprRewriter<Horn2VmtRewriter> {
 public:
  Horn2VmtRewriter(const HornTransStateSpace& space) : space_(space) {}

  z3::expr operator()(const z3::expr& e) { return Rewrite(e); }

  // Precondition: e is a sub-formula of a Horn clause body.
  // If e is a relation occurrence, rewrites it in T-land using the relation
  // and place variables. Otherwise, simply rewrites e using previously
  // rewritten children.
  z3::expr visit(const z3::expr& e) {
    if (e.is_app()) {
      if (auto e_var = space_.find_relation_var(e)) {
        z3::expr_vector conj(e.ctx());
        ExprVectorInserter out(conj);
        *out++ = *e_var;
        for (auto&& zipped : space_.iter_args_with_places(e)) {
          z3::expr arg = boost::get<0>(zipped);
          const StateVar& place_var = boost::get<1>(zipped);
          *out++ = (arg == place_var.current());
        }
        return expr_mk_and(conj);
      }
      return e.decl()(NewArgsExprVector(e));
    }
    return e;
  }

 private:
  const HornTransStateSpace& space_;
};

//^----------------------------------------------------------------------------^
//
//! Represents the translation of a set of Horn clauses into a transition
//! relation. The transition relation is "functional" in that each state
//! variable has exactly one top-level equation for it; the activation vars are
//! also at the top level as implications.
//!
//! Anything head isn't simply H(...) for some uninterpreted H gets put into
//! queries()
class HornSetTrans {
 public:
  HornSetTrans(const HornTransStateSpace& space,
                     const std::vector<HornRule>& rules) 
      : trans_(space.ctx()), to_vmt_(space) {
    ExprAndInserter trans_out(trans_);
    CreateQuantifiedVarInputs(space, rules);
    for (const auto& rule : rules) {
      if (rule.head().decl().decl_kind() != Z3_OP_UNINTERPRETED) {
        queries_.push_back(rule);
        continue;
      }
      const auto& activation_var = space.get_activation_var(rule);
      // Translates head and body.
      if (config.allocate_vars_by_sort) {
        // Don't worry about it if we're using the normal allocation strategy
        if (!rule.is_linear()) {
          throw std::runtime_error("nonlinear Horn clause detected, exiting");
        }
      }
      // Fills in var_subst_curr for rule: find var occurrences in relations:
      // 1. if it's a variable, maps [var -> place curr-state variable];
      // 2. otherwise, maps [var -> fresh input]
      ExprSubstitution var_subst_curr = make_var_subst(space, rule);
      // Removes relation occurrences from the rule's body and replaces them
      // with relation vars and place vars
      auto body_condition = to_vmt_(rule.body());
      logger.Log(3, "Rule {} condition from Horn:\n{}", rule.index(),
                 body_condition);
      // Removes bound vars from body_condition
      body_condition = var_subst_curr(body_condition);
      auto rule_condition = z3::implies(activation_var, body_condition);
      logger.Log(2, "Global rule {} condition to emit:\n{}",
                 rule.index(), rule_condition);
      // Done processing body, but it hasn't emitted the rule yet: it'll figure
      // out below which one to emit.

      *trans_out++ = rule_condition; // emit the rule condition

      // Adds this rule's next state to state-update cones
      CreateConesFromRule(space, rule, var_subst_curr);
    }

    // Sends next-state cones, which are complete, to the transition relation
    for (auto it = cones_.begin(), ie = cones_.end(); it != ie;
         // Erases them because they could free a lot of memory
         it = cones_.erase(it)) {
      auto&& [next_var, val] = *it;
      if (next_var.is_bool()) {
        val = val.simplify();
      }
      *trans_out++ = (next_var == val);
    }
    
    // Adds one-hot constraints for rules: exactly one rule should be chosen on
    // each transition.
    if (config.enable_one_hots) {
      OneHotConstraints ohc(space.ctx());
      ohc.insert(space.activation_input_vars_begin(),
                 space.activation_input_vars_end());
      if (space.activation_input_vars_begin() !=
          space.activation_input_vars_end()) {
        *trans_out++ = ohc.at_most(OneHotConstraints::Config::Commander(3));
        // *trans_out++ = ohc.at_most(OneHotConstraints::Config::Naive());
        for (auto&& v : ohc.commander_vars()) {
          space.xsys().AddInput(MakeInput(v));
        }
      }
    }
  }

  void CreateConesFromRule(const HornTransStateSpace& space,
                      const HornRule& rule,
                      const ExprSubstitution& var_subst_curr) {
      const auto& activation_var = space.get_activation_var(rule);
      const auto& relation_var = space.get_head_relation_var(rule);
      // The code below fills in cones_, the list of next-state equations for
      // the state variables updated by this rule.
      auto else_elt =
          cones_.insert({relation_var.next(),
                        relation_var.current()}).first;
      else_elt->second = z3::ite(activation_var, rule.ctx().bool_val(true),
                                 else_elt->second);
      for (auto&& zipped : space.iter_args_with_places(rule.head())) {
        z3::expr arg = boost::get<0>(zipped);
        const StateVar& place_var = boost::get<1>(zipped);
        else_elt = 
            cones_.insert({place_var.next(),
                          place_var.current()}).first;
        else_elt->second = z3::ite(activation_var, var_subst_curr(arg),
                                   else_elt->second);
      }
      logger.Log(3, "cones fir this rule");
      for (auto&& [next_var, val] : cones_) {
        logger.Log(3, "    {}: {}", next_var, val);
      }
  }

  // outputs to rule_input_vars_
  void CreateQuantifiedVarInputs(const HornTransStateSpace& space,
                                 const vector<HornRule>& rules) {
    SortMap<std::vector<PrimaryInputRef>> rule_places_by_sort;
    for (auto& rule : rules) {
      // Makes any inputs required to express the quantified variables in the
      // rule, binning them by sort
      if (z3::expr rule_expr = rule; rule_expr.is_quantifier()) {
        const unsigned num_bound_vars =
            Z3_get_quantifier_num_bound(rule_expr.ctx(), rule_expr); 
        if (config.allocate_inputs_by_sort) {
          SortMap<int> counts;
          for (unsigned i = 0; i < num_bound_vars; i++) {
            z3::sort sort(
                rule_expr.ctx(),
                Z3_get_quantifier_bound_sort(rule_expr.ctx(), rule_expr, i));
            if (counts.find(sort) == counts.end()) {
              counts[sort] = 0;
            }
            counts[sort]++;
          }
          for (auto&& [sort, num_occurrences] : counts) {
            int num_places =
                static_cast<int>(rule_places_by_sort[sort].size());
            for (int i = 0; i < (num_occurrences - num_places); i++) {
              auto name =
                  (SortName(sort) + "-input-" + to_string(num_places+i));
              auto& input_var = space.xsys().AddInput(MakeInput(
                      ctx().constant(name.c_str(), sort)));
              rule_places_by_sort[sort].push_back(input_var);
            }
          }
          counts.clear();
          for (unsigned i = 0; i < num_bound_vars; i++) {
            z3::sort sort(
                rule_expr.ctx(),
                Z3_get_quantifier_bound_sort(rule_expr.ctx(), rule_expr, i));
            auto var = rule_places_by_sort.at(sort)[counts[sort]];
            rule_input_vars_[rule.index()].push_back(var);
            counts[sort]++;
          }
          // Apparently the de-bruijn indices of variables are the revers from
          // the way they would be in a list...there's some verbiage to this
          // effect in the constructor for forall's in the Z3 documentation but
          // I didn't realize it would extend to this API. I guess it does. 
          std::reverse(rule_input_vars_[rule.index()].begin(),
                       rule_input_vars_[rule.index()].end());
        } else {
          // Create inputs named input-<rule-number>-<deBruijn index>
          for (unsigned i = 0; i < num_bound_vars; i++) {
            z3::sort sort(
                rule_expr.ctx(),
                Z3_get_quantifier_bound_sort(rule_expr.ctx(), rule_expr, i));
            z3::symbol var_name(
                rule_expr.ctx(),
                Z3_get_quantifier_bound_name(rule_expr.ctx(), rule_expr, i));
            auto name = fmt::format("input-{}-{}", rule.index(), var_name.str());
            auto& input_var = space.xsys().AddInput(
                MakeInput(ctx().constant(name.c_str(), sort)));
            rule_input_vars_[rule.index()].push_back(input_var);
          }
          std::reverse(rule_input_vars_[rule.index()].begin(),
                       rule_input_vars_[rule.index()].end());
        }
      }

    }
  }

  z3::expr trans() const { return trans_; }
  z3::context& ctx() const { return trans_.ctx(); }

  auto queries() {
    return boost::make_iterator_range(queries_.begin(), queries_.end());
  }

  z3::expr translate(const z3::expr& e) {
    return to_vmt_(e);
  }

  const PrimaryInput& get_rule_input_var(const HornRule& r,
                                         const z3::expr& bound_var) const {
    // The inputs are indexed by rule and de-Bruijn index of the bound var
    return rule_input_vars_.at(r.index()).at(
        Z3_get_index_value(bound_var.ctx(), bound_var));
  }

 private:
  // Transition relation that has been translated from the Horn set
  z3::expr trans_;
  // Maps rule index to quantifier var place inputs
  unordered_map<int, vector<PrimaryInputRef>> rule_input_vars_;
  ExprMap<z3::expr> cones_;
  std::vector<HornRule> queries_;
  Horn2VmtRewriter to_vmt_;
  ExprSubstitution make_var_subst(
      const HornTransStateSpace&, const HornRule& rule);
};
  
ExprSubstitution HornSetTrans::make_var_subst(
    const HornTransStateSpace& space, const HornRule& rule) {
  ExprSubstitution var_subst_curr(rule.ctx());
  // Set of vars mapped to places by visit_map_var()
  IterExprSet vars_with_places;
  // Set of all visited nodes for df traversal
  IterExprSet visited;
  // Precondition: e is a sub-expression of rule.body().
  // visit_map_var(), for a relation occurrence R(a,b,c,...), looks in a,b,c
  // for variable occurrences (as opposed to expressions) and maps them
  // directly to place vars, because this helps EUForia's pre-image
  // computation.
  auto visit_map_var = [&](const z3::expr& e) {
    if (e.is_app()) {
      if (auto e_var = space.find_relation_var(e)) {
        logger.Log(3, "--- visiting relation {}", e.decl());
        for (auto&& zipped : space.iter_args_with_places(e)) {
          z3::expr arg = boost::get<0>(zipped);
          const StateVar& place_var = boost::get<1>(zipped);
          if (arg.is_var()) {
            vars_with_places.insert(arg);
            logger.Log(3, "adding place_var [{} / {}] to var_subst_curr",
                       arg, place_var);
            var_subst_curr.AddSubstitution(arg, place_var.current());
          }
        }
      }
    }
  };
  // Precondition: e is a sub-expression of anything in rule that hasn't been
  // visited by visit_map_var().
  auto visit_create_input = [&](const z3::expr& e) {
    if (e.is_var()) {
      // for (unsigned i = 0; i < rule_input_vars.size(); i++) {
      //   auto input = rule_input_vars[i];
      //   logger.Log(3, "    rule_place {}: {}:{}", i, input, input.get_sort());
      // }
      // const z3::expr& i_expr = rule_input_vars[Z3_get_index_value(e.ctx(), e)];
      const z3::expr& i_expr = get_rule_input_var(rule, e);
      // auto fresh_input = 
      //     ctx().constant(("y-" + to_string(counter_++)).c_str(), e.get_sort());
      // auto& input = xsys_.AddInput(MakeInput(fresh_input));
      var_subst_curr.AddSubstitution(e, i_expr);
      logger.Log(3, "adding input [{} / {}] to var_subst_curr", e, i_expr);
    }
  };
  
  // put var -> place in subst for anything in body
  for_each(df_expr_ext_iterator::begin(rule.body(), visited),
           df_expr_ext_iterator::end(rule.body(), visited), visit_map_var);
  // fill in rest woth var -> input, over body and head, but skip visiting any
  // vars already mapped to places
  visited = vars_with_places; 
  for_each(df_expr_ext_iterator::begin(rule.body(), visited),
           df_expr_ext_iterator::end(rule.body(), visited), visit_create_input);
  for_each(df_expr_ext_iterator::begin(rule.head(), visited),
           df_expr_ext_iterator::end(rule.head(), visited), visit_create_input);
  return var_subst_curr;
}

} // end anonymous namespace

//^----------------------------------------------------------------------------^
//

class Horn2Vmt {
 public:
  Horn2Vmt(const HornTransStateSpace& space, const vector<HornRule>& all_rules) 
      : state_space_(space), rules_(all_rules) {
    // Sets transition relation
    HornSetTrans all_trans(state_space_, all_rules);
    xsys().set_trans(all_trans.trans());

    // Sets property
    for (const auto& rule : all_trans.queries()) {
      if (is_not(rule.head()) &&
          rule.head().arg(0).decl().decl_kind() == Z3_OP_UNINTERPRETED) {
        // property is denoted by (assert !R)
        xsys().set_property(all_trans.translate(rule.head()));
      } else if (z3::eq(rule.head(), ctx().bool_val(false))) {
        // property is denoted by (R => false)
        xsys().set_property(!all_trans.translate(rule.body()));
      } else {
        EUFORIA_FATAL("unrecognized rule: {} => {}", rule.body(), rule.head());
      }
    }
    
    // Sets initial state. In the initial state, all relations are false.
    z3::expr init(ctx());
    boost::transform(
        state_space_.relation_vars(), ExprAndInserter(init),
        [&](auto&& var) { return !var.current(); });
    xsys().set_init_state(init);

    // Performs normalizations that make Z3 a happy boi
    NnfRewriter nnf;
    ExprFlattener flatten;
    auto normalize = [&](auto&& e) {
      nnf.Reset(); flatten.Reset(); return flatten(nnf(e)); };
    xsys().RewriteSystem(normalize);
  }

  void Print(std::ostream& os) const {
    int64_t index = 0;
    fmt::print(os, "; {} rules\n", rules_.size());
    fmt::print(os, "; {} relations\n", state_space_.num_relations());
    fmt::print(os, "; {} state vars\n", xsys().num_vars());
    for (auto&& var : xsys().vars()) {
      fmt::print(os, "{}\n", var.current().decl());
      fmt::print(os, "{}\n", var.next().decl());
      fmt::print(os, "(define-fun .def{} () {} (! {} :next {}))\n", index,
                 var.current().get_sort(), var.current(),
                 var.next());
      ++index;
    }
    fmt::print(os, "; {} inputs\n", xsys().num_inputs());
    for (const z3::expr& input : xsys().inputs()) {
      fmt::print(os, "{}\n", input.decl());
    }
    fmt::print(os, "(define-fun .def{} () Bool (! {} :init true))\n",
               index++, xsys().init_state());
    fmt::print(os, "(define-fun .def{} () Bool (! {} :trans true))\n",
               index++, xsys().trans());
    fmt::print(os, "(define-fun .def{} () Bool (! {} :invar-property 0))\n",
               index, xsys().property());
  }

  // XXX instead of vmt print this in SMT2??????
  void PrintTrans(std::ostream& os) {
    int64_t index = 0;
    fmt::print(os, "; {} rules\n", rules_.size());
    fmt::print(os, "; {} relations\n", state_space_.num_relations());
    fmt::print(os, "; {} state vars\n", xsys().num_vars());
    fmt::print(os, "; begin state vars\n");
    // XXX print all declares in a block then print the defines after in a block so they're easier to delet
    for (auto&& var : xsys().vars()) {
      fmt::print(os, "{}\n", var.current().decl());
      fmt::print(os, "{}\n", var.next().decl());
      // fmt::print(os, "(define-fun .def{} () {} (! {} :next {}))\n", index,
      //            var.current().get_sort(), var.current(),
      //            var.next());
      ++index;
    }
    fmt::print(os, "; end state vars\n");
    fmt::print(os, "; {} inputs\n", xsys().num_inputs());
    fmt::print(os, "; begin inputs\n");
    for (const z3::expr& input : xsys().inputs()) {
      fmt::print(os, "{}\n", input.decl());
    }
    fmt::print(os, "; end inputs\n");
    fmt::print(os, "(declare-fun .trans () Bool)\n");
    fmt::print(os, "(assert (= .trans {}))\n", xsys().trans());
    // fmt::print(os, "(define-fun .def{} () Bool (! {} :trans true))\n",
    //            index++, xsys().trans());
  }


  z3::context& ctx() const { return state_space_.ctx(); }

 private:
  const HornTransStateSpace& state_space_;
  const vector<HornRule>& rules_;
  
  const VmtTransitionSystem& xsys() const { return state_space_.xsys(); }
  VmtTransitionSystem& xsys() { return state_space_.xsys(); }
};


//^----------------------------------------------------------------------------^
//
namespace po = boost::program_options;

po::options_description desc("options");

int main(int argc, char **argv) {
  // option parsing
  desc.add_options()
      ("help,h", "help")
      ("v", po::value<int>()->default_value(0), "set log level")
      ("int2bv", "convert ints to bvs as well")
      ("slice", po::value<string>()->default_value(""), 
       "output sliced transition using given prefix (suppresses normal output)")
      ("onehots", po::value<bool>()->default_value(true),
       "enable explicit one-hot transition constraints")
      ("varmap", po::value<string>(),
       "output mapping between relation places and state variables to this file")
      ("strategy", po::value<string>()->default_value("relation"),
       "sort - allocates one state variable per distinct place of a given sort\nrelation - allocates one state variable per relation place")
      ("input-file", po::value<string>(), "SMT2 file to convert");
  po::positional_options_description pd;
  pd.add("input-file", -1);
  po::variables_map opts;
  po::store(po::command_line_parser(argc, argv).
            options(desc).positional(pd).run(), opts);
  po::notify(opts);

  if (!opts.count("input-file")) {
    fmt::print(cerr, "error: missing input-file\n");
  }
  if (opts.count("help") || !opts.count("input-file")) {
    fmt::print(cout, "{} input-file\n", argv[0]);
    fmt::print(cout, "{}\n", desc);
    return EXIT_FAILURE;
  }

  logger.set_level(opts["v"].as<int>());

  config.enable_one_hots = opts["onehots"].as<bool>();

  config.allocate_vars_by_sort = true;
  if (opts["strategy"].as<string>() == "relation") {
    config.allocate_vars_by_sort = false;
  }
  if (auto strat = opts["strategy"].as<string>();
      !(strat == "sort" || strat == "relation")) {
    fmt::print(cerr, "error: unknown variable allocation strategy: {}\n",
               strat);
    return EXIT_FAILURE;
  }

  if (opts.count("varmap")) {
    config.varmap_filename = string(opts["varmap"].as<string>());
  }

  auto slice_prefix = opts["slice"].as<string>();
  config.slice_t = slice_prefix != "";

  z3::context ctx;
  config.input_filename = opts["input-file"].as<string>();
  HornClauses clause_db(ctx, config.input_filename.c_str(),
                        bool(opts.count("int2bv")));
  if (config.slice_t) {
    logger.Log(1, "config: slicing T into multiple files");
    int i = 0;
    auto head2trans = clause_db.group_by_heads();
    vector<HornTransition> queries;
    VmtTransitionSystem xsys(ctx);
    vector<HornRule> all_rules;
    boost::copy(clause_db.rules(), back_inserter(all_rules));
    HornTransStateSpace space(config, all_rules, &xsys);
    for (auto&& [head, horn_trans] : head2trans) {
      if (boost::algorithm::all_of(
              horn_trans.rules(),
              [](const HornRule& r) { return r.is_query(); })) {
        logger.Log(0, "skipping {} queries due to T slicing",
                   horn_trans.rules().size());
        continue;
      }
      
      // Inputs for quantified vars will be created during translation to Vmt;
      // make sure those go into xsys_copy since they shouldn't interact with
      // other slices of T.
      VmtTransitionSystem xsys_copy(xsys);
      space.set_output_xsys(&xsys_copy);
      logger.Log(1, "translating {} clauses for slice of {}",
                 horn_trans.rules().size(), head.name());
      std::vector<HornRule> rules;
      boost::copy(horn_trans.rules(), back_inserter(rules));
      Horn2Vmt h2v(space, rules);
      ofstream trans_out(fmt::format("{}{}.vmt", slice_prefix, i));
      fmt::print(trans_out, "; common head: {}\n", head.name());
      h2v.PrintTrans(trans_out);
      logger.Log(1, "slice of {} written to {}{}.vmt", head.name(),
                 slice_prefix, i);
      i++;
    }
  } else {
    VmtTransitionSystem xsys(ctx);
    std::vector<HornRule> all_rules;
    boost::copy(clause_db.rules(), back_inserter(all_rules));
    HornTransStateSpace space(config, all_rules, &xsys);
    Horn2Vmt h2v(space, all_rules);
    h2v.Print(std::cout);
  }

  if (config.varmap_filename) {
    logger.Log(1, "wrote varmap to {}", *config.varmap_filename);
  }

  return EXIT_SUCCESS;
}
