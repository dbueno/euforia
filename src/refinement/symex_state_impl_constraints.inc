// vim: set ft=cpp:

//! State Impl that uses a set of constraints as its representation and
//! understands the roles of current-state/next-state variables and inputs
class State::Impl {
 public:
  Executor& symex_; // holding me
  ExprSubstitution unprime_;
  ExprSubstitution passify_inputs_;
  const ConcreteVmtTransitionSystem& cts_;

  ExprSet constraints_; // constraints(X, Y_i, X_i) on this state

  ExprSet passified_inputs_; // all the passified inputs, all the way back to the beginning
  ExprSet passified_vars_;   // passified state vars, all the way back to the beginning
  
  int64_t passify_counter_ = 0;
  inline z3::expr PassifyConstant(const z3::expr& e) {
    assert(e.num_args() == 0);
    auto uniqueName = e.decl().name().str() + "v" + to_string(passify_counter_);
    return e.ctx().constant(uniqueName.c_str(), e.get_sort());
  }

  // inline Z3BtorExprPair MapConcreteExpr(const z3::expr& e) {
  //   return Z3BtorExprPair(e, z3_to_btor_.Rewrite(e));
  // }

  Impl(Executor& symex,
       const ConcreteVmtTransitionSystem& cxsys,
       const ExprSet& init_constraints) :
      symex_(symex),
      unprime_(cxsys.ctx()),
      passify_inputs_(cxsys.ctx()),
      cts_(cxsys) {
    for (auto it = cts_.vbegin(), ie = cts_.vend(); it != ie; ++it) {
      const StateVar& var = *it;
      unprime_.AddSubstitution(var.next(), var.current());
    }
    constraints_.insert(init_constraints.begin(), init_constraints.end());
    boost::for_each(constraints_, [&](auto&& e) { SanityCheck(e); });
    SimplifyConstraints();
  }

  Impl(const Impl& other) :
      symex_(other.symex_),
      unprime_(other.unprime_),
      passify_inputs_(other.ctx()),
      cts_(other.cts_),
      constraints_(other.constraints_),
      passified_inputs_(other.passified_inputs_),
      passified_vars_(other.passified_vars_),
      passify_counter_(other.passify_counter_) {
  }

  z3::context& ctx() const {
    return cts_.ctx();
  }


  template <typename It>
  class SanityChecker {
   public:
    SanityChecker(State::Impl& s, It it) : s_(s), it_(it) {}

    void operator()(const z3::expr& e) {
// #ifdef EXPENSIVECHECKS
      s_.SanityCheck(e);
// #endif
      *it_ = e;
    }
    
   private:
    State::Impl& s_;
    It it_;
  };

  void SanityCheck(const z3::expr& e) const {
    logger.Log(5, "symex var constraints State::Impl::SanityCheck");
    logger.Log(5, "SanityCheck({})\n", e);
    for (auto it = po_expr_iterator::begin(e),
      ie = po_expr_iterator::end(e); it != ie; ++it) {
      if ((*it).num_args() == 0) {
        if (IsValue(*it) ||
          passified_inputs_.find(*it) != passified_inputs_.end() ||
          passified_vars_.find(*it) != passified_vars_.end()) {
          continue;
        }
        if (auto var = cts_.FindVar(*it)) {
          if (z3::eq(var->current(), *it)) {
            continue;
          }
        }
        fmt::print(cerr, "term is not either a value or a current or "
          "passified input/var: {}:{}\n",
          *it, (*it).decl());
          EUFORIA_FATAL("error in symbolic execution state");
      }
    }
  }

  inline Executor& executor() const { return symex_; }

  const ExprSet& constraints() const;

  void InitializeConcretely();

  void AssumeState();

  void Simulate(bool simplify_next_states, const ExprSet& Ik,
    const ExprSet& Tk, const ExprSet& Ak_next);

  void SimplifyConstraints();

  void Print(std::ostream& os) const;

 private:
  void SortConstraintsByCurrent(vector<z3::expr>& time_sorted_constraints) const;

};

const ExprSet& State::Impl::constraints() const {
  return constraints_;
}
  

void State::Impl::SortConstraintsByCurrent(
      vector<z3::expr>& time_sorted_out) const {
  // sort constraints so that current-state ones come first so printing is nicer
  ExprSetTraversal find_passified_exprs(passified_vars_.begin(), passified_vars_.end());
  find_passified_exprs.AddTargets(passified_inputs_.begin(), passified_inputs_.end());
  std::stable_sort(time_sorted_out.begin(), time_sorted_out.end(),
                   [&](const z3::expr& x, const z3::expr& y) {
                   // x is less than y iff x has no passified elements and y does
                   return !find_passified_exprs.ExprContainsTarget(x) && find_passified_exprs.ExprContainsTarget(y);
                   });
}

void State::Impl::Print(std::ostream& os) const {
  vector<z3::expr> time_sorted_constraints;
  std::copy(constraints_.begin(), constraints_.end(), // put z3 nodes in time_sorted_constraints
            std::back_inserter(time_sorted_constraints));
  SortConstraintsByCurrent(time_sorted_constraints);

  fmt::print(os, "{} constraints:\n", constraints_.size());
  for (auto& c : time_sorted_constraints) {
    fmt::print(os, "    {}\n", c);
  }
  //for (auto& [var, val] : var_assignments_) {
  //  fmt::print(os, "    [concrete {}: {}]\n", var, val);
  //}
  //if (!input_assignments_.empty()) {
  //  fmt::print(os, "{} concrete input assignments:\n", input_assignments_.size());
  //  for (auto& [input, value] : input_assignments_) {
  //    fmt::print(os, "    {}: {}\n", input, value);
  //  }
  //}
}
void State::Impl::SimplifyConstraints() {
  z3::tactic simplify_constraints = z3::repeat(z3::tactic(ctx(), "simplify"));
  z3::tactic propagate_constants(ctx(), "propagate-values");
  z3::tactic solve_eqs(ctx(), "solve-eqs");
  z3::tactic ctx_simplify_constraints = z3::repeat(z3::tactic(ctx(),
      "ctx-simplify"));
  z3::tactic ctx_solver_simplify_constraints = z3::repeat(z3::tactic(ctx(),
      "ctx-solver-simplify"));
  z3::tactic der(ctx(), "der");
  z3::tactic reduce_bv_size(ctx(), "reduce-bv-size");
  auto custom_simplifier = propagate_constants  &ctx_simplify_constraints & reduce_bv_size;
  
  z3::goal g(ctx());
  for (auto& c : constraints_) {
    g.add(c);
  }
  constraints_.clear();
  auto new_goals = custom_simplifier(g);
  for (unsigned i = 0; i < g.size(); i++) {
    constraints_.insert(g[i]);
  }
}




void State::Impl::Simulate(bool /*simplify_next_states*/, const ExprSet& Ik,
  const ExprSet& Tk, const ExprSet& Ak_next) {
  auto orig_size = constraints_.size();
  ExprSubstitution passify_curr_state(ctx());
  for (auto it = cts_.vbegin(), ie = cts_.vend(); it != ie; ++it) {
    const StateVar& var = *it;
    auto passified_var = PassifyConstant(var.current());
    passify_curr_state.AddSubstitution(var.current(), passified_var);
    passified_vars_.insert(passified_var);
  }
  for (auto it = cts_.ibegin(), ie = cts_.iend(); it != ie; ++it) {
    const PrimaryInput& input = *it;
    auto passified_input = PassifyConstant(input.z);
    passify_inputs_.AddSubstitution(input.z, passified_input);
    passified_inputs_.insert(passified_input);
  }

  auto map_passified = [&](const z3::expr& e) {
    return passify_curr_state(e);
  };
  // constraints_(X)[X / X_i]: passify state variables in constraint_
  ExprSet new_constraints;
  std::transform(
      constraints_.begin(), constraints_.end(), 
      boost::make_function_output_iterator(SanityChecker(
          *this, std::inserter(new_constraints, new_constraints.end()))),
      map_passified);
  constraints_ = new_constraints;


  // Ik(X, Y, X')[X'/X, X/X_i, Y/Y_i]: time travel states, passify inputs
  auto time_travel_states = passify_curr_state & passify_inputs_ & unprime_;
  std::transform(
    Ik.begin(), Ik.end(),
    boost::make_function_output_iterator(SanityChecker(
        *this, std::inserter(constraints_, constraints_.end()))),
        time_travel_states);
  

  // T(X, Y, X')[X'/X, X/X_i, Y/Y_i]: time travel transition constraints
  vector<z3::expr> Tk_concrete;
  //std::transform(Tk.begin(), Tk.end(), std::inserter(Tk_concrete, Tk_concrete.begin()),
                 //[&](const z3::expr& e) { return ats_.Concretize(e); });
  transform(Tk.begin(), Tk.end(),
    boost::make_function_output_iterator(SanityChecker(
        *this, inserter(constraints_, constraints_.end()))),
        time_travel_states);

  // A'(X')[X'/X]: unprime the next-state constraint & put in constraints_
  std::transform(Ak_next.begin(), Ak_next.end(),
    boost::make_function_output_iterator(SanityChecker(
        *this, std::inserter(constraints_, constraints_.end()))),
        unprime_);

  // XXX arrays are always Xv0 = something so I need to rewrite them away
  // eagerly.Not sure what to do about the indices yet.
  // XXX test qe with standalone arrays and indices and see what it does

  ++passify_counter_;
  SimplifyConstraints();

  logger.Log(5, "state constraints went from {} -> {}",
             orig_size, constraints_.size());
}

// void State::Impl::AssumeState(vector<z3::expr>* assumps_out) {
//   BoolectorSolver& concrete_solver = symex_.concrete_solver_;
//   for (auto& n : constraints_) {
//     concrete_solver.Assume(n, true, string("assume-state"));
//   }
// }

// void State::Impl::InitializeConcretely() {
  // BoolectorSolver& concrete_solver = symex_.concrete_solver_;
  //constraints_.clear(); // XXX remove this if there are many initial states
  //for (auto it = cts_.vbegin(), ie = cts_.vend(); it != ie; ++it) {
  //  const StateVar& var = *it;
  //  auto val = concrete_solver.btor_solver()->assignment(
  //    z3_to_btor_.Rewrite(var.current()));
  //  auto z3_constraint = val->AsConstraint(var.current());
  //  constraints_.insert(MapConcreteExpr(z3_constraint));
  //  //vars_.erase(var.current());
  //  //vars_.insert({var.current(), Z3BtorExprPair(val->asValExpr(var.ctx(), Optional<StateVarRef>()), val->asNode())});
  //}
// }
