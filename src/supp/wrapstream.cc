// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/wrapstream.h"

using namespace std;

extern "C" {
#ifdef __APPLE__
  static int writeostreamfn(void *handler, const char *buf, int size) {
    auto& os = *static_cast<std::ostream*>(handler);
    for (int i = 0; i < size; i++) {
      os << buf[i];
    }
    return size;
  }
  
  FILE *wrapostream(std::ostream& os) {
    return funopen(&os, NULL, writeostreamfn, NULL, NULL);
  }
  
  static int writestringstream(void *ss, const char *buf, int size) {
    for (int i = 0; i < size; i++) {
      *static_cast<stringstream*>(ss) << buf[i];
    }
    return size;
  }
  
  FILE *wrapstringstream(stringstream *ss) {
    return funopen(ss, NULL, writestringstream, NULL, NULL);
  }

#elif __linux__

#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

  static ssize_t writeostreamfn(void *handler, const char *buf, size_t size) {
    auto& os = *(std::ostream*)handler;
    for (size_t i = 0; i < size; i++) {
      os << buf[i];
    }
    return size;
  }

  static ssize_t writestringstreamfn(void *ss, const char *buf, size_t size) {
    for (size_t i = 0; i < size; i++) {
      *(stringstream*)ss << buf[i];
    }
    return size;
  }

  FILE *wrapstringstream(stringstream *ss) {
    cookie_io_functions_t funs;
    funs.read = NULL;
    funs.write = writestringstreamfn;
    funs.seek = NULL;
    funs.close = NULL;
    return fopencookie(ss, "w", funs);
  }


  FILE *wrapostream(std::ostream& os) {
    cookie_io_functions_t funs;
    funs.read = NULL;
    funs.write = writeostreamfn;
    funs.seek = NULL;
    funs.close = NULL;
    return fopencookie(&os, "w", funs);
  }
#endif
}
