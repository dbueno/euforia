// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/reachability_graph.h"

#include <boost/range/algorithm/transform.hpp>

#include "abstract_model.h"
#include "supp/expr_normalize.h"
#include "xsys/transition_system.h"
#include "xsys/var_info_traversal.h"
#include "supp/expr_supp.h"
#include "supp/fmt_supp.h"


using namespace std;
using namespace llvm;

namespace euforia {

const ExprSet& ReachStep::input() const {
  return step_model_->input_predicates();
}

std::ostream& operator<<(std::ostream& out, const ReachStep& s) {
  fmt::print(out, "state cube:\n{}\n", s.state().asExpr());
  if (s.HasTransition()) {
    fmt::print(out, "inputs:\n{}\n", s.input());
    fmt::print(out, "model:\n{}\n", s.step_model());
    //fmt::print(out, "slice:\n{}\n", s.GetStateTransition());
  }
  return out;
}
  
//^----------------------------------------------------------------------------^
//

ReachStepIterator::ReachStepIterator(const ReachabilityGraph& g, TimedCube c,
                                     int index) 
    : graph_(g) {
  boost::optional<TimedCube> next;
  shared_ptr<AbstractModel> model(nullptr);
  shared_ptr<TSlice> slice(nullptr);
  if (auto search = graph_.transition_.find(c.thecube);
      search != graph_.transition_.end()) {
    next = get<1>(search->second);
    model = get<0>(search->second);
    slice = graph_.easy_next_.at(c.thecube);
  }
  step_ = ReachStep(c, next, model, slice, index);
}
  

// XXX this stuff is a little wonky because it's not clear the current state
// variables do not always refer to the current state variables in the model.
// Because there are n-1 models for n states. So someone needs to handle that,
// or not use the model yet.
ReachStepIterator& ReachStepIterator::operator++() {
  if (auto search = graph_.transition_.find(step_->state_.thecube);
      search != graph_.transition_.end()) {
    // there is a transition from this state to next
    auto& next_state = std::get<1>(search->second);
    boost::optional<TimedCube> next2;
    shared_ptr<AbstractModel> next_model(nullptr);
    shared_ptr<TSlice> next_slice(nullptr);
    if (auto search2 = graph_.transition_.find(next_state.thecube);
        search2 != graph_.transition_.end()) {
      // there is a transition from next, which gives us a model & a slice for
      // next
      next2 = get<1>(search2->second);
      next_model = get<0>(search2->second);
      next_slice = graph_.easy_next_.at(next_state.thecube);
    }
    step_ = ReachStep(next_state, next2, next_model, next_slice,
                      step_->state_index_+1);
  } else {
    step_.reset();
  }
  return *this;
}

//^----------------------------------------------------------------------------^
//ReachabilityGraph

ReachabilityGraph::ReachabilityGraph(int depth, uint64_t num_backward_reach_,
                                     const TransitionSystem& sts)
    : depth_(depth), nrbc_(num_backward_reach_), init_(TimedCube{nullptr,-1}), sts_(sts) {}

ReachabilityGraph::~ReachabilityGraph() = default;


void ReachabilityGraph::AddUnreachable(uint64_t step, TimedCube generalization,
                                       TimedCube tgt) {
  generalized_.emplace(tgt, make_pair(generalization, step));
}

void ReachabilityGraph::AddReachable(
    uint64_t step, TimedCube z, TimedCube s, shared_ptr<AbstractModel> model,
    shared_ptr<TSlice> sSliceT) {
  transition_.insert({z.thecube, make_tuple(move(model), s, step)});
  easy_next_.insert({z.thecube, sSliceT});
}

ReachStepIterator ReachabilityGraph::cx_begin() const {
  return ReachStepIterator(*this, init_, 0);
}

ReachStepIterator ReachabilityGraph::cx_end() const {
  return ReachStepIterator(*this);
}
  
size_t ReachabilityGraph::cx_length() const {
  return count_if(cx_begin(), cx_end(), [](auto&&) { return true; });
}
  
pair<vector<ReachStep>::const_reverse_iterator,
     vector<ReachStep>::const_reverse_iterator>
ReachabilityGraph::cx_reverse_range() const {
  return make_pair(cx_steps_.rbegin(), cx_steps_.rend());
}


void ReachabilityGraph::SetInit(TimedCube i) {
  init_ = i;

  // find all cubes touched by the CX, delete all others
  unordered_set<shared_ptr<Cube>> touched;
  touched.insert(init_.thecube);
  auto t = init_.thecube;
  auto loc = transition_.find(t);
  while (loc != transition_.end()) {
    t = std::get<1>(loc->second).thecube;
    touched.insert(t);
    loc = transition_.find(t);
  }
  //    LOGFL(spdlog::get("*pdrlow"), "{} touched", touched.size());
  for (auto it = transition_.begin(); it != transition_.end();) {
    if (touched.find(it->first) == touched.end()) {
      it = transition_.erase(it);
    } else {
      ++it;
    }
  }
  for (auto it = generalized_.begin(); it != generalized_.end();) {
    if (touched.find(it->first.thecube) == touched.end()) {
      it = generalized_.erase(it);
    } else {
      ++it;
    }
  }
  
  // set up reverse iterator. It would be more efficient to do this on demand,
  // but that method (cx_reverse_range) is const so it can't be set there.
  cx_steps_.clear();
  copy(cx_begin(), cx_end(), back_inserter(cx_steps_));
}

void ReachabilityGraph::as_dot(std::ostream &str, const string& label) const {
  str << "digraph RGRAPH {" << endl;
  str << "node [color=gray90, style=filled, shape=box];" << endl;

  unordered_map<Cube*, int> IDs;
  int ID = 0;
  auto getCubeID = [&IDs, ID] (const shared_ptr<Cube>& t) mutable -> int {
    int ret;
    auto loc = IDs.find(t.get());
    if (loc == IDs.end()) {
      IDs.insert({t.get(), ID});
      ret = ID++;
    } else {
      ret = loc->second;
    }
    return ret;
  };
  auto appendProps = [&str] (const unordered_map<string, string>& props) {
    if (props.size() > 0) {
      str << " [";
      string sep = "";
      bool first = true;
      for (const auto& [key, val] : props) {
        if (!first) {
          str << ", ";
        }
        str << key << "=\"" << val << "\"";
        first = false;
      }
      str << "]";
    }
  };

  // Gather all the individual cubes
  unordered_set<shared_ptr<Cube>> cubes;
  for (const auto& cubeAndImage : transition_) {
    cubes.insert(cubeAndImage.first);
    cubes.insert(std::get<1>(cubeAndImage.second).thecube);
  }
  for (const auto& cubeAndGen : generalized_) {
    cubes.insert(cubeAndGen.first.thecube);
    //cubes.emplace(cubeAndGen.second, true);
  }

  // Put STG in there
  //    stg.asInnerDot(str);

  // Create labels for cubes & put stg in there too
  auto node_label = [](auto cube_id, auto size, auto text) {
    return "cube" + cube_id + " size" + size + "\n" + text;
  };
  for (const auto& c : cubes) {
    ostringstream labelos;
    str << "cube" << getCubeID(c);
    unordered_map<string, string> props;

    for (const auto& lit : *c) {
      labelos << "[c]: " << lit << endl;
    }
    //os << "\"" << c.first << "\"";
    auto cube_label = node_label(to_string(getCubeID(c)), to_string(c->size()),
                            labelos.str());
    const auto label_orig_size = cube_label.size();
    // The max size should be 16384, according to the error message dot gives
    // me. But it still produces the error message when there are 16384
    // characters in the cube_label. I tried 16383, too, because I thought maybe I
    // had not accounted for the null character. No joy. Oh well.
    const int kDotMaxStringSize = 14000;
    if (cube_label.size() > kDotMaxStringSize) {
      cube_label.erase(cube_label.begin() + kDotMaxStringSize,
                       cube_label.end());
      cube_label.replace(kDotMaxStringSize-4, 4, " ...");
      props["euforia_label_orig_size"] = to_string(label_orig_size);
    }
    props["euforia_label_size"] = to_string(cube_label.size());
    props.emplace("cube_label", cube_label);
    props["fillcolor"] = "lightcyan";

    props["shape"] = "box";
    appendProps(props);
    str << ";" << endl;



    // register stg node and point cube to it
    //      for (auto ip : sts.findIP(*c)) {
    //        const stg_node& n = stg.getNode(ip);
    //        if (llvm::isa<wait_node>(n)) continue; // no edges to wait it just clutters things
    //        props.clear();
    //        props["style"] = "dashed";
    //        props["arrowhead"] = "diamond";
    //        props["fillcolor"] = "lightcyan";
    //        str << "cube" << getCubeID(c) << " -> " << stg.dotName(n);
    //        appendProps(props);
    //        str << ";" << endl;
    //      }
  }

  // Add unreachable edgese
  auto edge_label = [](auto n, auto frame) {
    return "pob" + n + "@frame" + frame;
  };
  for (const auto& p : generalized_) {
    auto unreachableCube = p.first.thecube;
    auto generalizedCube = p.second.first;
    auto nth_pob = p.second.second;

    unordered_map<string, string> nopeProps, edgeProps;
    nopeProps["shape"] = "star";
    nopeProps["label"] = "";
    nopeProps["fillcolor"] = "thistle1";
    edgeProps["fontcolor"] = "indianred3";
    edgeProps["fillcolor"] = edgeProps["fontcolor"];;
    edgeProps["color"] = edgeProps["fillcolor"];
    edgeProps["label"] = edge_label(to_string(nth_pob), to_string(generalizedCube.frame));
    str << "nope" << getCubeID(unreachableCube);
    appendProps(nopeProps);
    str << ";" << endl;
    str << "nope" << getCubeID(unreachableCube) << " -> cube" << getCubeID(unreachableCube);
    appendProps(edgeProps);
    str << ";" << endl;
  }

  // Add reachable edges
  for (const auto& cubeAndImage : transition_) {
    unordered_map<string, string> props;

    auto z = cubeAndImage.first;
    auto model = std::get<0>(cubeAndImage.second);
    //auto f = model->getInputLits();
    auto s = std::get<1>(cubeAndImage.second);
    auto nth_pob = std::get<2>(cubeAndImage.second);

    props["label"] = edge_label(to_string(nth_pob), to_string(s.frame));
    //ostringstream inputStream;
    //inputStream << endl;
    //for (auto& lit : f) {
    //  inputStream << lit << endl;
    //}
    //props["label"] += inputStream.str();
    props["fillcolor"] = "palegreen4";
    props["color"] = props.at("fillcolor");
    props["fontcolor"] = props["fillcolor"];
    str << "cube" << getCubeID(z) << " -> cube" << getCubeID(s.thecube);
    appendProps(props);
    str << ";" << endl;
  }

  str << "label=\"" << label << "\";" << endl;
  str << "labelloc=top;" << endl << "labeljust=left;" << endl;
  str << "}" << endl;


}

z3::expr ReachabilityGraph::bmc_formula() const {
  z3::expr_vector fs(ctx());
  ExprVectorInserter fs_ins(fs);
  // Creates a formula for one BMC query from the reachability graph.
  int64_t i = 1;
  for (auto it = cx_begin(), ie = cx_end(); it != ie; ++it, ++i) {
    const auto& reach_step = *it;
    // Renames current state variables v to v-(i-1). Renames input variables
    // v to v-(i-1).
    const auto& subst_current = mk_renamer(i-1);

    if (i == 1) {
      boost::transform(ExprConjuncts(sts_.init_state()), fs_ins,
                       subst_current);
    }
    
    boost::transform(reach_step.state(), fs_ins, subst_current);

    if (reach_step.has_transition()) {
      // Renames inputs v to v-i
      ExprSubstitution subst_input = mk_input_renamer(i);
      // Renames next-state vars v to v-i.
      ExprSubstitution subst_next = mk_next_renamer(i);
      ExprSubstitution subst_all = subst_current & subst_next & subst_input;
      auto new_trans = subst_all(sts_.trans());
      boost::copy(ExprConjuncts(new_trans), fs_ins);
      
      auto inputs = subst_all(expr_mk_and(ctx(), reach_step.input()));
      boost::copy(ExprConjuncts(inputs), fs_ins);
    }
  }
  return expr_mk_and(fs);
}

ExprSubstitution ReachabilityGraph::mk_renamer(int64_t i) const {
  ExprSubstitution subst(ctx());
  for (const StateVar& var : sts_.vars()) {
    auto passified_var = get_step_var(i, var.current());
    subst.AddSubstitution(var.current(), passified_var);
  }
  return subst;
}

ExprSubstitution ReachabilityGraph::mk_input_renamer(int64_t i) const {
  ExprSubstitution subst(ctx());
  for (const PrimaryInput& input : sts_.inputs()) {
    auto passified_var = get_step_var(i, input);
    subst.AddSubstitution(input, passified_var);
  }
  return subst;
}

//! Renames next-state inputs with i suffix
ExprSubstitution ReachabilityGraph::mk_next_renamer(int64_t i) const {
  ExprSubstitution subst(ctx());
  for (const StateVar& var : sts_.vars()) {
    auto passified_var = get_step_var(i, var.current());
    subst.AddSubstitution(var.next(), passified_var);
  }
  return subst;
}

z3::expr ReachabilityGraph::get_step_var(
    int64_t i, const z3::expr& e) const {
  assert(e.num_args() == 0);
  auto new_name = fmt::format("{}_{}", e.decl().name().str(), i);
  return e.ctx().constant(new_name.c_str(), e.get_sort());
}

z3::context& ReachabilityGraph::ctx() const { return sts_.ctx(); }

std::ostream& operator<<(std::ostream& out, const ReachabilityGraph& g) {
  if (!g.has_init()) {
    EUFORIA_FATAL("can't yet print a ReachabilityGraph that isn't a counterexample (no init)");
  }
  z3::solver s(g.ctx(), "QF_UF");
  s.add(g.bmc_formula());
  out << s.to_smt2();
  // return out;
  ExprNormalize norm;
  for (auto it = g.cx_begin(), ie = g.cx_end(); it != ie; ++it) {
    fmt::print(out, "; ACX state A[{}] (cube {}, size {})\n", it->state_index(),
               it->state().ID, it->state().size());
    auto a_i = norm(it->state().asExpr());
    fmt::print(out, "(define-fun .state{} () Bool\n{})\n", it->state_index(),
               a_i);
    if (it->HasTransition()) {
      fmt::print(out, "; In[{}] (size {})\n", it->input_index(),
                 it->input().size());
      auto inp_i = norm(expr_mk_and(a_i.ctx(), it->input()));
      fmt::print(out, "(define-fun .inputs{} () Bool\n{})\n", it->input_index(), inp_i);
    }
  }
  return out;
}

} // end namespace euforia
