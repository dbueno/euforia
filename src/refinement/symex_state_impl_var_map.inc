/// State that uses var maps as its representation
class State::Impl {
 public:

  Executor& symex_;
  const AbstractVmtTransitionSystem& ats_;
  const VmtTransitionSystem& cts_;
  BtorConcretizingRewriter rw_;
  vector<Z3BtorExprPair> init_constraints_; // only for initial states

  // two star data structures
  PathConstraintSet pc_;                  // path constraint, only on inputs
  expr_umap<StateConstraint> vars_;       // map state var to expr

  expr_uset passified_inputs_;            // all the passified inputs, all the way back to the beginning
  
  expr_umap<z3::expr> var_assignments_;   // concrete assignments to vars
  expr_umap<z3::expr> input_assignments_; // concrete assignments to versioned inputs
  
  int64_t passify_counter_ = 0;
  inline z3::expr PassifyConstant(const z3::expr& e) {
    assert(e.num_args() == 0);
    auto uniqueName = e.decl().name().str() + "v" + to_string(passify_counter_);
    return e.ctx().constant(uniqueName.c_str(), e.get_sort());
  }
  
  Impl(Executor& symex, const expr_uset& init_constraints) :
      symex_(symex),
      ats_(symex.concrete_solver.ATS),
      cts_(symex.concrete_solver.ATS.getConcreteSystem()),
      rw_(symex.concrete_solver.ATS, symex.concrete_solver.getSolver()),
      passify_counter_(0) {
    for (auto& e : init_constraints) {
      init_constraints_.push_back(rw_.concretizeFormula(e));
    }
  }

  Impl(const Impl& other) :
      symex_(other.symex_),
      ats_(other.ats_),
      cts_(other.cts_),
      rw_(other.rw_),
      pc_(other.pc_),
      vars_(other.vars_),
      passified_inputs_(other.passified_inputs_),
      passify_counter_(other.passify_counter_)
      // do not copy init_constraints_!
      // do not copy var_assignments_
      // do not copy input_assignments_
  {}

  z3::context& ctx() {
    return cts_.ctx();
  }

  void SanityCheck(const z3::expr& e) {
    for (auto I = po_expr_iterator::begin(e), E = po_expr_iterator::end(e); I != E; ++I) {
      if (e.num_args() == 0) {
        if (IsValue(e))
          continue;
        if (passified_inputs_.find(e) != passified_inputs_.end()) {
          continue;
        }
        fmt::print(cerr, "term is not either a value or a passified input: {}\n", e);
        FATAL("error in symbolic execution state");
      }
    }
  }

  void AddPcNode(const StateConstraint& n) {
    pc_.insert(n);
  }

  void InitializeConcretely();

  void AssumeState();

  void Simulate(bool simplify_next_states, const expr_uset& Ik, const expr_uset& Tk, const expr_uset& Ak_next);
  // returns <inputs_used, induced_pc_exprs>
  pair<expr_uset, expr_uset>
      UpdateVars(BoolectorSolver& concrete_solver, const expr_uset& Ik, const expr_uset& Tk, const expr_uset& Ak_next);

  const expr_umap<StateConstraint>& Assignments() const {
    return vars_;
  }

  const expr_umap<z3::expr>& ConcreteAssignments() const {
    return var_assignments_;
  }

  const expr_umap<z3::expr>& ConcreteInputAssignments() const {
    return input_assignments_;
  }

  void Print(std::ostream& os) const;

};


void State::Impl::Print(std::ostream& os) const {
  int size = 0;
  for (auto& elt : pc_)
    size++;
  fmt::print(os, "variable assignments:\n");
  unsigned numFalseLocs = 0;
  for (auto& [v, val] : vars_) {
    const StateVar& var = cts_.getVar(v);
    auto name = var.name;
    // skip false locations -- easier to read
    if (var.isLocation() && is_literal_false(val.z3Node())) {
      numFalseLocs++;
    } else {
      os << "    " << name << ": " << val.z3Node();
      if (auto search = var_assignments_.find(v); search != var_assignments_.end()) {
        os << " [concrete: " << search->second << "]";
      }
      os << endl;
    }
  }
  fmt::print(os, "path constraint has {} literals:\n", size);
  for (auto& c : pc_) {
    os << "    " << c.z3Node() << endl;
  }
  if (!input_assignments_.empty()) {
    fmt::print(os, "concrete input assignments:\n");
    for (auto& [input, value] : input_assignments_) {
      fmt::print(os, "    {}: {}\n", input, value);
    }
  }
  os << "(" << numFalseLocs << " false locations elided)";
}
  

void State::Impl::Simulate(bool simplify_next_states, const expr_uset& Ik, const expr_uset& Tk, const expr_uset& Ak_next) {
  BoolectorSolver& concrete_solver = symex_.concrete_solver;
  logger.Log(5, "Simulate");
  auto& rewriter = rw_;
  //Simulate(Ik, Tk, Ak_next);
  const auto& [inputs_used, pc_staging] = UpdateVars(concrete_solver, Ik, Tk, Ak_next);
  stringstream us;

  Print(us);
  logger.Log(5, "state efter phase 1, updating vars: {}", us.str());
  logger.Log(5, "new pc constraints (to be passified): {}", pc_staging);
  
  // 2nd phase - passify inputs and substitute, and record concrete input assignment
  
  for (auto& input_passified : passified_inputs_) {
    // for old passified inputs, record assignment
    auto input_passified_btor = rw_.rewriteAsBtor(input_passified);
    auto x = concrete_solver.getSolver()->assignment(input_passified_btor)->asValExpr(ctx(), Optional<StateVarRef>());
    input_assignments_.insert({input_passified, x});
  }
  
  z3::expr_vector passify_substitution_src(ctx()), passify_substitution_dst(ctx());
  for (auto I = cts_.ibegin(), E = cts_.iend(); I != E; ++I) {
    // create versioned substitution
    auto passified = PassifyConstant(I->z);
    passified_inputs_.insert(passified);
    passify_substitution_src.push_back(I->z);
    passify_substitution_dst.push_back(passified);
  
    // update concrete input assignments
    auto input_btor = rw_.rewriteAsBtor(I->z);
    auto val = concrete_solver.getSolver()->assignment(input_btor)->asValExpr(ctx(), Optional<StateVarRef>());
    input_assignments_.insert({passified, val});
  }
  
  ++passify_counter_;
  
  // variable rhs's may refer to inputs, so version the inputs
  for (auto& mapping_curr : vars_) {
    auto val = mapping_curr.second.z3Node();
    auto newval = val.substitute(passify_substitution_src, passify_substitution_dst);
    if (simplify_next_states)
      newval = newval.simplify();
    mapping_curr.second = Z3BtorExprPair(newval, rewriter.rewriteAsBtor(newval));
  }
  
  // pc refers to inputs, so version the inputs
  for (z3::expr expr : pc_staging) {
    expr = expr.substitute(passify_substitution_src, passify_substitution_dst);
    if (simplify_next_states)
      expr = expr.simplify();
    AddPcNode(Z3BtorExprPair(expr, rewriter.rewriteAsBtor(expr)));
  }
}
  

pair<expr_uset, expr_uset> 
State::Impl::UpdateVars(BoolectorSolver& concrete_solver, const expr_uset& Ik, const expr_uset& Tk, const expr_uset& Ak_next) {
  // substitution mapping current-state-var -> prev state value
  z3::expr_vector prev_var_substitution_src(ctx()), prev_var_substitution_dst(ctx());
  for (auto& mapping : vars_) {
    prev_var_substitution_src.push_back(mapping.first);
    prev_var_substitution_dst.push_back(mapping.second.z3Node());
  }

  // record concrete assignments and assign into vars_ for locations
  vars_.clear();
  for (auto I = cts_.vbegin(), E = cts_.vend(); I != E; ++I) {
    auto znext_btor = rw_.rewriteAsBtor(I->next());
    auto x = concrete_solver.getSolver()->assignment(znext_btor)->asValExpr(ctx(), Optional<StateVarRef>());
    var_assignments_.insert({I->current(), x});
    if (I->isLocation()) {
      vars_.insert({I->current(), Z3BtorExprPair(x, rw_.rewriteAsBtor(x))});
    }
  }


  ExprInfoTraversal expr_info(cts_);
  expr_uset pc_staging;
  
  // 1st phase - update changed vars_ map and add new PC constraints
  // using the transition constraints, add x = <next-state> assignmentss to this state
  for (const z3::expr& e : Tk) {
    expr_info.traverse(ats_.concretize(e));
    z3::expr lhs(ctx()), rhs(ctx());
    assert(is_eq(e));
    // at end, lhs = var+, rhs = rhs
    //if (is_eq(e)) {
     if (!ats_.hasStateVar(e.arg(0)) && !ats_.hasStateVar(e.arg(1)))
      continue;
     lhs = e.arg(0);
     rhs = e.arg(1);
     if (ats_.hasStateVar(e.arg(1)) && ends_with(e.arg(1).decl().name().str(), "+")) {
      lhs = e.arg(1);
      rhs = e.arg(0);
     }
    //}
    //if (bool(lhs)) {
    auto& var = cts_.getVar(ats_.concretize(lhs));
    auto rhs_concrete = ats_.concretize(rhs);
    auto rhs_concrete_substituted = rhs_concrete.substitute(prev_var_substitution_src, prev_var_substitution_dst);
    vars_.insert({var.current(), Z3BtorExprPair(rhs_concrete_substituted, rw_.rewriteAsBtor(rhs_concrete_substituted))});
    //}
  }
  // fill in rest of values from the model
  for (auto it = cts_.vbegin(), ie = cts_.vend(); it != ie; ++it) {
    const StateVar& var = *it;
    if (vars_.find(var.current()) != vars_.end())
      continue;
    auto val = concrete_solver.getSolver()->assignment(rw_.rewriteAsBtor(var.next()));
    vars_.insert({var.current(), Z3BtorExprPair(val->asValExpr(ctx(), Optional<StateVarRef>()), val->asNode())});
  }
  // maps current-state-vars -> new value
  z3::expr_vector vars_substitution_src(ctx()), vars_substitution_dst(ctx());
  for (auto& mapping_curr : vars_) {
    auto var = mapping_curr.first;
    auto val = mapping_curr.second.z3Node();
    vars_substitution_src.push_back(var);
    vars_substitution_dst.push_back(val);
  }


  // add input predicates to path constraint
  for (auto& predicate : Ik) {
    // this is slightly wonky but it works. we nede to get rid of current and next-state vars from predicate
    // first do current
    auto predicate_concrete = ats_.concretize(predicate).substitute(prev_var_substitution_src, prev_var_substitution_dst);
    // now rename next to current and do next
    predicate_concrete = cts_.substCurr(predicate_concrete).substitute(vars_substitution_src, vars_substitution_dst);
    expr_info.traverse(predicate_concrete);
    pc_staging.insert(predicate_concrete);
  }

  // add state-induced constraints to the PC, so that inputs are properly constrained
  //logger.Log(5, "substitution for updating the path constraint with state-induced constraints");
  //for (int i = 0; i < input_substitution_src.size(); i++) {
  //  logger.Log(5, "{} -> {}", input_substitution_src[i], input_substitution_dst[i]);
  //}
  // substitute new mappings into target constraints
  ExprSetTraversal find_any_inputs(expr_info.inputs_used_);
  find_any_inputs.AddTargets(passified_inputs_);
  logger.Log(5, "looking for constraints involving these previous inputs: {}", find_any_inputs.GetTargets());
  for (auto predicate : Ak_next) {
    // predicate(X+) needs to be converted to current-state
    auto concrete_predicate = cts_.substCurr(ats_.concretize(predicate));
    auto newpredicate = concrete_predicate.substitute(vars_substitution_src, vars_substitution_dst);
    if (find_any_inputs.ExprContainsTarget(newpredicate)) {
      // add newpredicate to PC
      pc_staging.insert(newpredicate);
    } else {
      //logger.Log(5, "    >> {} does not contain any previous inputs", newpredicate);
    }
  }

  // at this point, vars_ may refer to prev-state variables
  // pc may refer to inputs
  //

  return std::make_pair(expr_info.inputs_used_, pc_staging);
}


void State::Impl::AssumeState() {
  BoolectorSolver& concrete_solver = symex_.concrete_solver;
  for (auto& [var, formula] : vars_) {
    Z3BtorExprPair equality(var == formula.z3Node(), rw_.rewriteAsBtor(var) == formula.btorNode());
    concrete_solver.assume(equality, true);
  }
  for (auto& n : pc_) {
    concrete_solver.assume(n, true);
  }
  for (auto& n : init_constraints_) {
    concrete_solver.assume(n, true);
  }
}



void State::Impl::InitializeConcretely() {
  BoolectorSolver& concrete_solver = symex_.concrete_solver;
  for (auto IT = cts_.vbegin(), IE = cts_.vend(); IT != IE; ++IT) {
    const StateVar& var = *IT;
    auto val = concrete_solver.getSolver()->assignment(rw_.rewriteAsBtor(var.current()));
    vars_.erase(var.current());
    vars_.insert({var.current(), Z3BtorExprPair(val->asValExpr(var.ctx(), Optional<StateVarRef>()), val->asNode())});
  }
}
