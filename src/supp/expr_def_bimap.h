// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_EXPR_DEF_BIMAP_H_
#define EUFORIA_SUPP_EXPR_DEF_BIMAP_H_

#include <boost/bimap.hpp>

#include "supp/expr_supp.h"

namespace euforia {
using ExprDefBimap = boost::bimap<boost::bimaps::set_of<z3::ExprWrapper>,
                                  boost::bimaps::set_of<z3::ExprWrapper>>;
}

#endif
