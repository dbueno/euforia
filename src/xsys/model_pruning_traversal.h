// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include <algorithm>
#include <boost/variant/variant.hpp>
#include <llvm/ADT/SmallVector.h>
#include <tuple>
#include <utility>
#include <vector>
#include <z3++.h>

#include "checker_types.h"
#include "supp/expr_supp.h"
#include "supp/std_supp.h"

//^----------------------------------------------------------------------------^

namespace euforia {

class ModelPruningTraversalT {
 public:
  ModelPruningTraversalT(Z3EvalFunc eval) : eval_(eval) {}

  //^--------------------------------------------------------------------------^
  
  // Stack elements for depth-first stack. Caches eval() results for nodes and
  // their arguments.
  //
  // A stack element keeps the state of traversing (some of) the args of a
  // given node. The arg to visit next is at arg_index.
  struct StackElt {
    z3::expr node;
    z3::expr node_eval;
    llvm::SmallVector<std::pair<z3::expr, z3::expr>, 4> args;
    size_t arg_index;

    StackElt(const std::pair<z3::expr, z3::expr>& evald_pair)
        : node(evald_pair.first), node_eval(evald_pair.first.ctx()),
          arg_index(0) {
      if (bool(evald_pair.second)) {
        node_eval = evald_pair.second;
      }
    }

    StackElt(const z3::expr& n, const z3::expr& ev) 
        : node(n), node_eval(ev), arg_index(0) {}

    StackElt(StackElt&&) = default;
    StackElt(const StackElt&) = delete;
    StackElt& operator=(const StackElt&) = delete;

    bool operator==(const StackElt& other) const {
      return z3::eq(node, other.node) && 
          z3::eq(node_eval, other.node_eval) &&
          arg_index == other.arg_index && args == other.args;
    }

    bool operator!=(const StackElt& other) const { return !(*this == other); }

    void push_arg(const z3::expr& e, const z3::expr& e_eval) {
      args.push_back(std::make_pair(e, e_eval));
    }

    void push_arg(const z3::expr& e) {
      args.push_back(std::make_pair(e, z3::expr(e.ctx())));
    }
  };

  //^--------------------------------------------------------------------------^
  
  template <class SetType>
  class IteratorStorage {
   public:
    IteratorStorage(SetType& s) : visited_(s) {}
   
   protected:
    // Used to keep track of what's already processed
    SetType& visited_;
  };

  template <class SetType>
  class Iterator : public IteratorStorage<SetType> {
   public:
    using value_type = StackElt;
    using difference_type = std::ptrdiff_t;
    using reference = value_type&;
    using pointer = value_type*;
    using iterator_category = std::input_iterator_tag;

    Iterator(ModelPruningTraversalT& t, const z3::expr& e, SetType& s)
        : IteratorStorage<SetType>(s), expr_true_(e.ctx().bool_val(true)),
          expr_false_(e.ctx().bool_val(false)), mpt_(t) {
      if (visited_.insert(e).second) {
        stack_.push_back(StackElt(e, z3::expr(e.ctx())));
        PruneArgs(&stack_.back());
        TraverseArg();
      }
    }
    
    Iterator(ModelPruningTraversalT& t, z3::context& c, SetType& s) 
        : IteratorStorage<SetType>(s), expr_true_(c.bool_val(true)),
          expr_false_(c.bool_val(false)), mpt_(t) {}

    bool operator==(const Iterator& it) { return stack_ == it.stack_; }

    bool operator!=(const Iterator& it) { return !(*this == it); }

    const StackElt& operator*() const {
      return stack_.back();
    }

    Iterator& operator++() { // preincrement
      stack_.pop_back();
      if (!stack_.empty())
        TraverseArg();
      return *this;
    }

   private:
    // Brings in visited_ from superclass
    using IteratorStorage<SetType>::visited_;
    // Depth-first traversal stack
    std::vector<StackElt> stack_;
    z3::expr expr_true_;
    z3::expr expr_false_;
    ModelPruningTraversalT& mpt_;

    void TraverseArg() {
      // Precondition: stack is not empty
      assert(!stack_.empty());
      while (stack_.back().arg_index != stack_.back().args.size()) {
        auto& arg_elt = stack_.back().args[stack_.back().arg_index++];
        if (visited_.insert(arg_elt.first).second) {
          stack_.push_back(StackElt(arg_elt));
          PruneArgs(&stack_.back());
        }
      }
    }

    // Fills in StackElt with the args we will visit of the node
    void PruneArgs(StackElt *elt) const {
      auto node = elt->node, node_eval = elt->node_eval;
      const std::function<bool(const z3::expr& e)> expr_is_true =
          [&](const z3::expr& e) { return z3::eq(e, expr_true_); },
          expr_is_false = 
              [&](const z3::expr& e) { return z3::eq(e, expr_false_); };
      auto push_rest = [&](unsigned start, const z3::expr& node) {
        elt->args.reserve(node.num_args());
        for (unsigned i = start; i < node.num_args(); i++) {
          elt->push_arg(node.arg(i));
        }
      };
      
      const auto kind = node.decl().decl_kind();
      switch (kind) {
        case Z3_OP_ITE: {
          const auto cond = node.arg(0);
          const auto cond_eval = Eval(cond, false);
          elt->push_arg(cond, cond_eval);
          if (expr_is_true(cond_eval) || expr_is_false(cond_eval)) {
            // Skips traversing the false branch of ITE.
            const auto true_branch = node.arg(expr_is_true(cond_eval) ? 1 : 2);
            const auto false_branch = node.arg(expr_is_true(cond_eval) ? 2 : 1);
            // Adds condition and true branch only to stack_
            elt->push_arg(true_branch, z3::expr(node.ctx()));
          } else {
            push_rest(1, node);
          }
          break;
        }

        case Z3_OP_AND:
        case Z3_OP_OR: {
          assert(kind == Z3_OP_AND || kind == Z3_OP_OR);
          // single_case tests for the cases where only a "single" arg
          // should be visited. single_case for AND is if it's false.
          // single_case for OR is if it's true.
          const auto single_case = kind == Z3_OP_AND ? expr_is_false : 
              expr_is_true;
          // Evaluates the node if we haven't already
          if (!bool(node_eval)) {
            elt->node_eval = node_eval = Eval(node, false);
          }
          if (expr_is_true(node_eval) || expr_is_false(node_eval)) {
            if (single_case(node_eval)) {
              // Finds single arg and only expand that node
              for (unsigned i = 0; i < node.num_args(); i++) {
                const auto arg = node.arg(i);
                const auto arg_eval = Eval(arg, false);
                // Finds a single justifying arg, if it exists, and ignores
                // all other args.
                if (single_case(arg_eval)) {
                  elt->push_arg(arg, arg_eval);
                  break;
                }
              }
              // If control gets here, either we found a single_case arg or the
              // AND (resp. OR) was tautologically false (resp. true) so it
              // doesn't expand any nodes.
              break;
            }
            // AND is true/OR is false
            // *These three lines* makes all the difference in the world.
            // Caches the node's evaluation so it can be reused for the
            // next round.
            elt->args.reserve(node.num_args());
            for (unsigned i = 0; i < node.num_args(); i++) {
              elt->push_arg(node.arg(i), node_eval);
            }
          } else {
            push_rest(0, node);
          }
          break;
        }

        default:
          push_rest(0, node);
          break;
      }
    }

    z3::expr Eval(const z3::expr& e, bool c) const {
      return mpt_.Eval(e, c);
    }
  };
  
  //^--------------------------------------------------------------------------^
  
  template <class SetType>
  Iterator<SetType> begin(const z3::expr& e, SetType& s) {
    return Iterator<SetType>(*this, e, s);
  }
  
  template <class SetType>
  Iterator<SetType> end(const z3::expr& e, SetType& s) {
    return Iterator<SetType>(*this, e.ctx(), s);
  }

  int num_evals() const { return num_evals_; }

  z3::expr Eval(const z3::expr& e, bool c) {
    num_evals_++;
    return eval_(e, c);
  }

 private:
  Z3EvalFunc eval_;
  int num_evals_ = 0;
};

} // namespace euforia
