// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "abstract_model.h"

#include "cube.h"
#include "supp/expr_iterators.h" // df/po iterators
#include "supp/expr_supp.h"
#include "xsys/transition_system.h"

using namespace std;

namespace euforia {
//^----------------------------------------------------------------------------^
//abstract model impl

class AbstractModel::Impl {
 public:
  int64_t num_evals_ = 0;
  Impl(Model&) {}
};

/*-----------------------------------------------------------------------------------*/
// UninterpretedPartition
UninterpretedPartition::~UninterpretedPartition() {}

int UninterpretedPartition::size() const {
  return cells_.size();
}


std::ostream& UninterpretedPartition::Print(std::ostream& os) const {
  os << "UninterpretedPartition<" << cells_.size() << " cells_>:" << endl;
  for (auto& subset : cells_) {
    auto rep = subset.first;
    const auto& elts = subset.second;
    os << rep << ": ";
    bool first = true;
    for (auto elt : elts) {
      if (!first) os << ", ";
      if (!z3::eq(rep, elt))
        os << elt;
      first = false;
    }
    os << endl;
  }
  return os;
}

void UninterpretedPartition::Insert(const z3::expr& x, bool model_completion) {
  assert(IsUninterp(x));
  
  auto xrep = model_.Eval(x, model_completion);
  
  cells_[xrep].insert(x);
}


bool UninterpretedPartition::Same(const z3::expr& e, const z3::expr& f) const {
  assert(cells_.find(model_.Eval(e)) != cells_.end() && "partition doesn't know about e");
  assert(cells_.find(model_.Eval(f)) != cells_.end() && "partition doesn't know about f");
  return z3::eq(model_.Eval(e), model_.Eval(f));
}

z3::expr UninterpretedPartition::Find(const z3::expr& e) const {
  auto terms = cells_.at(model_.Eval(e));
  assert(!terms.empty());
  return *begin(terms);
}

z3::expr UninterpretedPartition::FindConstantIfPossible(const z3::expr& e) const {
  assert(cells_.find(e) != cells_.end()); // assume e is in cell: avoids eval()
  auto terms = cells_.at(e);
  assert(!terms.empty());
  for (auto& t : terms)
    if (IsUConstant(t))
      return t;
  return *begin(terms);
}

ExprSet UninterpretedPartition::AsFormula() const {
  ExprSet ret;
//    z3::expr_vector reps(model.ctx());
  AstMap<z3::expr_vector> repsBySort;
  for (auto& cell : cells_) {
    auto& elts = cell.second;
    const auto rep = FindConstantIfPossible(cell.first);
//      reps.push_back(rep);
    if (auto search = repsBySort.find(rep.get_sort());
        search == repsBySort.end()) {
      repsBySort.insert({rep.get_sort(), z3::expr_vector(model_.ctx())});
    }
    auto& sortedRepList = repsBySort.at(rep.get_sort());
    sortedRepList.push_back(rep);
    // set other things in cell equal to each other
    auto eltsCopy{elts};
    eltsCopy.erase(rep);
    for (auto it = eltsCopy.begin(), ie = eltsCopy.end(); it != ie; ) {
      auto curr = it++;
      if (it == ie) { ret.insert(expr_eq(*curr, rep)); break; }
      ret.insert(expr_eq(*curr, *it));
    }
  }
//    if (reps.size() >= 2) {
    for (auto& [sort, reps] : repsBySort) {
      (void)sort;
      // I'm pretty sure I'm not using a big (distinct ...) here because often
      // they are constants which are unnecessary to put in there and because
      // it limits the MUS-based generalization
      if (reps.size() >= 2)
        for (unsigned i = 0; i < reps.size(); i++) {
          for (unsigned j = i+1; j < reps.size(); j++) {
            if (z3::eq(reps[i].get_sort(), reps[j].get_sort()))
              if (!IsUConstant(reps[i]) || !IsUConstant(reps[j])) // $K consts are unequal by axiom
                ret.insert(expr_distinct(reps[i], reps[j]));
          }
        }
    }
  return ret;
}

void UninterpretedPartition::RemoveIf(const std::function<bool(const z3::expr&)>& pred) {
  auto cellsCopy{cells_};
  for (auto& [rep, cell] : cellsCopy) {
    for (auto it = cell.begin(); it != cell.end();) {
      if (pred(*it)) {
        it = cell.erase(it);
      } else
        ++it;
    }
    cells_.erase(rep);
    if (cell.begin() != cell.end()) {
      // cell nonempty
      auto newCell{cell};
      auto inserted = cells_.insert({rep, newCell}).second;
      assert(inserted);
      _unused(inserted);
    }
  }
}


/*-----------------------------------------------------------------------------------*/
// abstract model

AbstractModel::~AbstractModel() {}

AbstractModel::AbstractModel(const shared_ptr<Model>& model,
                             const TransitionSystem& TSin,
                             const ConcreteFuncDeclMap *func_decls_,
                             bool populateDecls)
  : model_(model), TS(TSin), upart_(*this), func_decls_(func_decls_), 
    pimpl_(make_unique<AbstractModel::Impl>(*model)) {
  if (func_decls_ && populateDecls) {
    for (auto& entry : *func_decls_) {
      const z3::func_decl& d = static_cast<const z3::func_decl&>(entry.first);
      if (d.arity() == 0)
        Add(d());
    }
  }
}

z3::context& AbstractModel::ctx(){ return TS.ctx(); }
const z3::context& AbstractModel::ctx() const { return TS.ctx(); }


void AbstractModel::Add(const z3::expr& e) {
  for (auto I = df_expr_iterator::begin(e), E = df_expr_iterator::end(e); I != E; ++I) {
    visit(*I);
  }
}

void AbstractModel::AddInputPredicate(const z3::expr& e) {
  input_predicates_.insert(e);
}


#if 0
class ArrayEvaluator : public ExprRewriter<ArrayEvaluator, bool> {
 public:
  ArrayEvaluator(const Model& m) : model_(m) {}

  bool visitAS_ARRAY(const z3::expr& e) {
    auto some_array_1_eval_func_decl = e.decl();
    assert(Z3_is_app(e.ctx(), e));
    assert(Z3_get_decl_num_parameters(e.ctx(), some_array_1_eval_func_decl) == 1);
    assert(Z3_get_decl_parameter_kind(e.ctx(), some_array_1_eval_func_decl, 0) == 
           Z3_PARAMETER_FUNC_DECL);
    z3::func_decl model_fd = z3::func_decl(e.ctx(), 
                                   Z3_get_decl_func_decl_parameter(e.ctx(), some_array_1_eval_func_decl, 0));
    z3::func_interp fun_interp = model_.get_func_interp(model_fd);
    for (unsigned i = 0; i < fun_interp.num_entries(); i++) {
      auto entry = fun_interp.entry(i);
      logger.Log(4, "entry {}:");
      logger.Log(4, "  value: {}", entry.value());
      for (unsigned j = 0; j < entry.num_args(); j++) {
        logger.Log(4, "  arg {}: {}", j, entry.arg(j));
      }
    }
    return false;
  }


  bool visitCONST_ARRAY(const z3::expr& e) {
    logger.Log(4, "const array: {}", e);
    return false;
  }


  bool visitSTORE(const z3::expr& e) {
    logger.Log(4, "store {}", e);
    return false;
  }


  bool visitExpr(const z3::expr& e) {
    logger.Log(4, "expr {}", e);
    return false;
  }

 private:
  Model model_;
};
#endif


bool AbstractModel::Satisfies(const z3::expr& e, bool completion) {
  if (is_literal_true(e)) {
    return true;
  } else if (is_literal_false(e)) {
    return false;
  }

  auto e_eval = Eval(e, completion);
  logger.Log(4, "Satisfies e? {} -> {}", e, e_eval);
  if (is_literal_true(e_eval)) {
    return true;
  }

  return false;
}


z3::expr AbstractModel::Eval(const z3::expr& e, bool completion) {
  ++pimpl_->num_evals_;
  auto ret = model_->Eval(e, completion);
  //assert(z3::eq(eval_result, ret));
  return ret;
}
  
unsigned AbstractModel::num_evals() const {
  return pimpl_->num_evals_;
}

/*-----------------------------------------------------------------------------------*/

void AbstractModel::visitExpr(const z3::expr& e) {
  if (e.is_bool()) {
    if (is_literal_true(e))
      return;

    auto polarity = Eval(e, false);
    assert(is_literal_true(polarity) || is_literal_false(polarity));
    auto atom = is_literal_true(polarity) ? e : expr_not(e);
    auto unnegated = expr_strip_negation(e);
    if (func_decls_ && func_decls_->find(unnegated.decl()) != func_decls_->end()) { // call to abstract function
      upreds_.insert(atom);
    } else if (IsLiteral(e)) {
      preds_.insert(atom);
    } else {
      // ignore for now
      //assert(false && "unhandled expr");
    }
  } else if (IsUninterp(e)) {
    upart_.Insert(e);
  } else {
    logger.Log(6, "abstract model IGNORED expr {}", e);
  }
}


/*-----------------------------------------------------------------------------------*/


// In order to to presen-state Cube expansion, we construct an AbstractModel
// and remove things from it. This function matches the things that should 
// be removed.  
static auto matchForPresent(const TransitionSystem& TS) {
  auto matchInputAuxNextState = [&TS](const z3::expr& ex) -> bool {
    for (auto I = po_expr_iterator::begin(ex), E = po_expr_iterator::end(ex); I != E; ++I) {
      auto e = *I;
      if (((TS.HasNextStateVar(e))) ||
          TS.FindInput(e))
        return true;
    }
    return false;
  };
  return matchInputAuxNextState;
}

void AbstractModel::ExpandIntoCube(Cube& out) {
  auto isBadForProjection = matchForPresent(TS);
  //if (!upreds_.empty()) { cerr << *this << endl; }
  for (auto& UP : upreds_) {
    if (!isBadForProjection(UP)) {
      out.push(UP, TS.prime(UP));
    }
  }
  auto UPartCopy{upart_};
  UPartCopy.RemoveIf(isBadForProjection);
  auto f = UPartCopy.AsFormula();
  for (auto& lit : f)
    out.push(lit, TS.prime(lit));
  for (auto& p : preds_) {
    auto normP = expr_strip_negation(p); // strip ! aronud literal
    if (!isBadForProjection(normP))// && TS.hasStateVar(normP))
      out.push(p, TS.prime(p));
  }
}

/*-----------------------------------------------------------------------------------*/

static void printFuncInterp(std::ostream& os, const z3::func_interp& FI) {
  for (unsigned i = 0; i < FI.num_entries(); i++) {
    auto entry = FI.entry(i);
    os << "    (";
    for (unsigned j = 0; j < entry.num_args(); j++) {
      auto arg = entry.arg(j);
      os << arg << (j+1 < entry.num_args() ? ", " : "");
    }
    os << ") => " << entry.value() << endl;
  }
  os << "    (*) => " << FI.else_value() << endl;
}


ostream& AbstractModel::Print(std::ostream &os) const {
  os << "AbstractModel:" << endl;
  //    os << "model: " << model << endl;
  
  //if (func_decls_ && shouldPrintFuncInterp) {
  //  for (auto& [decl, _] : *func_decls_) {
  //    (void)_;
  //    const z3::func_decl& d = static_cast<const z3::func_decl&>(decl);
  //    if (Z3_model_has_interp(ctx(), model_, d)) {
  //      if (d.arity() > 0) {
  //        os << d << ":" << endl;
  //        printFuncInterp(os, model_.get_func_interp(d));
  //      }
  //    }
  //  }
  //}
  os << to_string(input_predicates_.size()) << " input predicates:" << endl << "    ";
  for (auto& pred : input_predicates_) {
    os << pred << ", ";
  }
  os << endl;
  os << to_string(upreds_.size()+preds_.size()) << " predicates (* if bad for projection):" << endl;
  os << "    ";
  auto isBadForProjection = matchForPresent(TS);
  bool first = true;
  for (auto& pred : upreds_) {
    if (!first) os << ", ";
    os << pred << (isBadForProjection(pred) ? " (*)" : "");
    first = false;
  }
  os << endl << "    ";
  first = true;
  for (const z3::expr& pred : preds_) {
    // try to cleanly omit negated locations
    if (pred.decl().decl_kind() == Z3_OP_NOT &&
        TS.IsControlLocation(pred.arg(0))) {
      assert(is_literal_false(model_->Eval(pred.arg(0))));
      continue;
    }
    if (!first) os << ", ";
    os << pred << (isBadForProjection(pred) ? " (*)" : "");
    first = false;
  }
  os << " [false locations omitted]";
  os << endl;
  os << upart_;
  return os;
}
}

void mylog(const euforia::UninterpretedPartition& up) { up.Print(std::cerr); }
