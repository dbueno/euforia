#!/bin/sh

# Sets the library identifier of each of the libraries to an @rpath relative
# value so that Xcode will properly be able to find them.

NAME=libLLVM-3.7svn.dylib
install_name_tool -id @rpath/$NAME `pwd`/llvm-dsa/install/lib/$NAME
NAME=libz3.dylib
install_name_tool -id @rpath/$NAME `pwd`/z3/build/$NAME
