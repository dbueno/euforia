// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/expr_dot_formatter.h"
#include "expr_graph_traits.h"
#include "supp/expr_iterators.h"

#include <sstream>
#include <unordered_map>

using namespace std;
using namespace llvm;


static void FormatProperties(std::ostream& os, 
                             const unordered_map<string, string>& properties) {
  if (properties.empty())
    return;

  fmt::print(os, " [");
  bool first = true;
  for (auto& entry : properties) {
    fmt::print(os, "{}{}={}", !first ? "," : "", entry.first, entry.second);
    first = false;
  }
  fmt::print(os, "]");
}

//^----------------------------------------------------------------------------^


namespace euforia {

class ExprDotFormatter::Impl {
 public:
  Impl(std::ostream& os, bool leaf_by_occurrence = true) 
      : os_(os), leaf_by_occurrence_(leaf_by_occurrence) {}

  void Print(const ExprSet&);
  void FormatNode(const z3::expr&, const z3::expr&, int64_t);

  std::ostream& os_;
  bool leaf_by_occurrence_;
};

void ExprDotFormatter::Impl::FormatNode(
    const z3::expr& top_node, const z3::expr& node, int64_t node_id) {
  unordered_map<string, string> properties;
  stringstream label;
  // Print the name with its hash so my traversals can follow along
  fmt::print(label, "\"{}\n. {:08x} .\"", node.decl().name().str(), node.hash());
  properties["label"] = label.str();
  if (node.num_args() == 0)
    properties["fillcolor"] = "cadetblue1";

  if (z3::eq(node, top_node))
    properties["shape"] = "egg";

  fmt::print(os_, "N{}", node_id);
  FormatProperties(os_, properties);
  fmt::print(os_, ";\n");
}


void ExprDotFormatter::Impl::Print(const ExprSet& exprs) {
  fmt::print(os_, "digraph EXPR {{\n");
  fmt::print(os_, "node [color=gray90,style=filled,shape=box];\n");
    
  int64_t id_counter = 0;
  // Whether to print leaf occurrences as distinct nodes
  for (const z3::expr& e : exprs) {
    // Below, due to the leaf_by_occurrence option, we handle leaves when
    // visiting their parents.  This means that in case the top level expr is a
    // leaf itself, it wouldn't be printed; unless we handle the special case
    // here.
    if (e.num_args() == 0) {
      FormatNode(e, e, e.hash());
    }

    for (auto it = po_expr_iterator::begin(e), ie = po_expr_iterator::end(e);
         it != ie; ++it) {
      if (leaf_by_occurrence_ && (*it).num_args() == 0)  {
        // leaves handled when visiting parent
        continue;
      }
      
      FormatNode(e, *it, (*it).hash());
      
      // We are traversing in post order so all children of (*it) will have
      // been visited.  If leaf_by_occurrence is set to true, then each leaf in
      // the expression is printed as a distinct dot node. This avoids a bunch
      // of edges all pointing at a single leaf.  If it's false, then it will
      // put a single dot node for each distinct leaf, which means you can
      // easily see how may different ways a given variable (or constant) is
      // referred to. Handling this boils down to assigning a distinct ID to
      // each leaf (child of this node) as it's encountered.
      int i = 0;
      for (const auto& arg : ExprArgs(*it)) {
        int64_t arg_id = leaf_by_occurrence_ && arg.num_args() == 0 ?
            ++id_counter : arg.hash();
        if (leaf_by_occurrence_) {
          FormatNode(e, arg, arg_id);
        }
        stringstream label;
        if ((*it).num_args() != 1) {
          fmt::print(label, " [label=\"{}/{}\"]", i++, (*it).num_args()-1);
        }
        fmt::print(os_, "N{} -> N{}{};\n", (*it).hash(), arg_id, label.str());
      }
    }
  }

  fmt::print(os_, "}}");
}

//^----------------------------------------------------------------------------^
  
ExprDotFormatter::ExprDotFormatter(std::ostream& os) 
  : pimpl_(std::make_unique<Impl>(os)) {}

ExprDotFormatter::~ExprDotFormatter() = default;

void ExprDotFormatter::Print(const ExprSet& exprs) {
  pimpl_->Print(exprs);
}

}

