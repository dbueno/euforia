// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "expr_stats.h"

namespace euforia {  

  std::ostream& operator<<(std::ostream& os, const ExprStats& stats) {
    fmt::print(os, "num_z3_decls: {} - distinct z3 decls in system\n", stats.docc.size());
    //os << "<<< this is each unique functional thing: state vars, logical/bitwise/arithmetic functions, etc. >>>" << endl;
#define YOU_WANT_TOO_MUCH_INFO 0
#if YOU_WANT_TOO_MUCH_INFO
    for (auto& [d, cnt] : stats.docc) {
      auto s = Z3_func_decl_to_string(d.ctx(), (z3::func_decl&)d);
      os << s << ": " << cnt << endl;
    }
#endif
    fmt::print(os, "num_ops: {} - number of distinct ops like or, bitwise and, sign-ext, etc.\n", stats.focc.size());
    //os << "<<< functional ops like Boolean or, bitwise and, sign-ext, etc. >>>" << endl;
    fmt::print(os, "num_exprs: {} - number of unique expressions\n", stats.eocc.size());
    //os << "<<< number of unique expressions >>>" << endl;
#if YOU_WANT_TOO_MUCH_INFO
    for (auto& [e, cnt] : stats.eocc) {
      if (cnt > 1)
        os << e << ": " << cnt << endl;
    }
#endif
    
    return os;
  }

}
