// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

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
#include "one_hot.h"
#include "refinement/layered_refinement.h"
#include "supp/expr_flattener.h"
#include "supp/expr_iterators.h"
#include "supp/expr_rewriter.h"
#include "supp/expr_substitution.h"
#include "supp/expr_supp.h"
#include "supp/nnf_rewriter.h"
#include "xsys/state_vars.h"
#include "xsys/vmt_transition_system.h"

using namespace std;
using namespace euforia;



//^----------------------------------------------------------------------------^
//
namespace po = boost::program_options;

po::options_description desc("options");

int main(int argc, char **argv) {
  // option parsing
  desc.add_options()
      ("help,h", "help")
      ("v", po::value<int>()->default_value(0), "set log level")
      ("filename", po::value<string>(), "SMT2 file to convert");
  po::positional_options_description pd;
  pd.add("filename", -1);
  po::variables_map vmap;
  po::store(po::command_line_parser(argc, argv).
            options(desc).positional(pd).run(), vmap);
  po::notify(vmap);

  if (!vmap.count("filename")) {
    fmt::print(cerr, "error: missing filename\n");
  }
  if (vmap.count("help") || !vmap.count("filename")) {
    fmt::print(cout, "{} filename", argv[0]);
    fmt::print(cout, "{}\n", desc);
    return EXIT_FAILURE;
  }

  logger.set_level(vmap["v"].as<int>());

  try {
    z3::context ctx;
    auto filename = vmap["filename"].as<string>();
    string filebuf;
    {
      std::ifstream fin(filename);
      std::stringstream sstr;
      sstr << fin.rdbuf();
      filebuf = sstr.str();
    }
    auto formula = ctx.parse_string(filebuf.c_str());
    auto abstract = Arrays2Fresh(ctx);
    auto new_formulas = abstract(formula);
    z3::solver s(ctx);
    for (unsigned i = 0; i < new_formulas.size(); i++) {
      s.add(new_formulas[i]);
    }
    fmt::print(s.to_smt2());
  } catch (const z3::exception& e) {
    fmt::print(std::cerr, "z3 exception:\n");
    fmt::print(std::cerr, "{}\n", e.msg());
    std::flush(std::cerr);
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}
