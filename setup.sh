#!/usr/bin/env bash

set -e
set -x

if [ $(uname) = "Darwin" ]; then
    on_osx="yes"
    on_linux=""
else
    on_osx=""
    on_linux="yes"
fi

portable_nproc() {
    OS=$(uname -s)
    if [ -n "$on_linux" ]; then
        num_procs=$(nproc --all)
    elif [ -n "$on_osx" ]; then
        num_procs=$(sysctl -n hw.ncpu)
    else
        num_procs=$(getconf _NPROCESSORS_ONLN)  # glibc/coreutils fallback
    fi
    echo "$num_procs"
}

TOP=`pwd`

if [ -z "$num_procs" ]; then
    num_procs=$(portable_nproc)
fi
[ -z "$build_dir" ] && build_dir="$TOP/code/euforia/build"
# If llvm_dir is defined, assume it's installed
# llvm_dir should be the installed dir, not lib/cmake/llvm
[ -z "$llvm_dir" ] && install_llvm=1
[ -z "$llvm_dir" ] && llvm_dir="$build_dir/llvm-5.0.1/install"
# If z3_dir is defined, assume it's installed
[ -z "$z3_dir" ] && install_z3=1
[ -z "$z3_dir" ] && z3_dir="$build_dir/z3-master"
# If mathsat_dir is defined, assume it's installed
[ -z "$mathsat_dir" ] && install_mathsat=1
# Disable yices for now
# [ -z "$yices_dir" ] && install_yices=1
# [ -z "$yices_dir" ] && yices_dir="$build_dir/yices2"
if [ -n "$install_mathsat" ]; then
    if [ -n "$on_osx" ]; then
        mathsat_link="http://mathsat.fbk.eu/download.php?file=mathsat-5.6.0-darwin-libcxx-x86_64.tar.gz"
        mathsat_dir="$build_dir/mathsat-5.6.0-darwin-libcxx-x86_64"
    else
        mathsat_link="http://mathsat.fbk.eu/download.php?file=mathsat-5.6.0-linux-x86_64.tar.gz"
        mathsat_dir="$build_dir/mathsat-5.6.0-linux-x86_64"
    fi
fi
[ -z "$boolector_dir" ] && boolector_dir="$TOP/code/euforia/lib/boolector"

if [ -z "$CC" -a -z "$CXX" ]; then
    if [ -n "$on_osx" ]; then
        export CC=clang
        export CXX=clang++
    fi
fi
euforia_build_type="Release"
euforia_dir="$build_dir/$euforia_build_type"

git submodule init
git submodule update

mkdir -p "$build_dir"

# Install LLVM
if [ -n "$install_llvm" ]; then
    mkdir -p $build_dir/llvm
    cd $build_dir/llvm
    llvm_file=llvm-5.0.1.src.tar.xz
    if [ ! -f $llvm_file ]; then
        wget "http://releases.llvm.org/5.0.1/llvm-5.0.1.src.tar.xz"
    fi
    if [ ! -d llvm-5.0.1.src ]; then
        tar xf llvm-5.0.1.src.tar.xz
        if [ -n "$on_osx" ]; then
            cd llvm-5.0.1.src && patch -p1 < $TOP/llvm-5.0.1.patch
        fi
    fi
    cd $build_dir/llvm
    if [ ! -d llvm-5.0.1.build ]; then
        mkdir -p llvm-5.0.1.build
        cd llvm-5.0.1.build
        cmake -DCMAKE_INSTALL_PREFIX="$llvm_dir" -DLLVM_BUILD_LLVM_DYLIB=1 -DLLVM_ABI_BREAKING_CHECKS=FORCE_OFF \
            -DLLVM_ENABLE_RTTI=1 -DCMAKE_BUILD_TYPE=Release -DLLVM_ENABLE_CXX1Z=1 ../llvm-5.0.1.src
        make -j$num_procs install
    fi
fi

# Install Z3
if [ -n "$install_z3" ]; then
    # Build z3
    cd $TOP/code/euforia/lib/z3
    if [ ! -d build ]; then
        #rm -rf build 
        python3 scripts/mk_make.py -p $z3_dir --python --pypkgdir $z3_dir/python
    fi
    cd ./build
    if [ ! -d "$z3_dir" ]; then
        make -j$num_procs install
    fi
    if [ -n "$on_osx" ]; then
        install_name_tool -id @rpath/libz3.dylib $z3_dir/lib/libz3.dylib
    fi
fi

# Install mathsat
cd $build_dir
if [ -n "$install_mathsat" ]; then
    if [ ! -f mathsat.tar.gz ]; then
      wget -O mathsat.tar.gz "$mathsat_link"
    fi
    if [ ! -d "$mathsat_dir" ]; then
      tar xzf mathsat.tar.gz
    fi
    if [ -n "$on_osx" ]; then
        install_name_tool -id @rpath/libmathsat.dylib $mathsat_dir/lib/libmathsat.dylib
    fi
fi

# Install yices
if [ -n "$install_yices" ]; then
    cd $TOP/code/euforia/lib/yices2
    autoconf
    ./configure --prefix=$yices_dir
    make -j$num_procs
    make install
fi


# I don't depend on this anymore
# cd $TOP/code/euforia/lib/sexpr-1.3
# if test ! -f .build-done; then
#     ./configure
#     make
#     touch .build-done
# fi

cd $TOP/code/euforia/lib/fmt
rm -rf build && mkdir -p build && cd build
if test ! -f .build-done; then
    cmake -DFMT_TEST=False ..
    make -j$num_procs
    touch .build-done
fi

cd $TOP/code/euforia/lib/boolector
if test ! -f .build-done; then
    NPROC=$num_procs ./contrib/setup-btor2tools.sh
    NPROC=$num_procs ./contrib/setup-lingeling.sh
    ./configure.sh --only-lingeling
    cd build && make -j$num_procs
    touch .build-done
fi

mkdir -p $euforia_dir
cd $euforia_dir
cmake -DCMAKE_BUILD_TYPE=$euforia_build_type \
    -DLLVM_DIR=$llvm_dir/lib/cmake/llvm \
    -DZ3_DIR=$z3_dir \
    -DMATHSAT_DIR=$mathsat_dir \
    -DBOOLECTOR_DIR=$boolector_dir \
    $TOP/code/euforia
make -j$num_procs

echo "euforia is at $euforia_dir/bin/euforia"
