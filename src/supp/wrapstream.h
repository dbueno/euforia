// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_SUPP_WRAPSTREAM_H_
#define EUFORIA_SUPP_WRAPSTREAM_H_

extern "C" {
#include <stdio.h>
}

#include <iostream>
#include <sstream>

extern "C" {
FILE *wrapostream(std::ostream& os);
FILE *wrapstringstream(std::stringstream *ss);
}

#endif
