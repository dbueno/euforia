{ self
, pkgs
, z3
, mathsat
, propagateConst
, immer
, fmt
, outputCheck
, lib
, ninja
, cmake
, boost17x
, gmp
, lit
, stdenv
, bzip2
, boolector
, universal-ctags
, debugVersion ? false
, sanitizer ? false
}:
let
  denisbueno = "Denis Bueno <dbueno@gmail.com>";
  libllvm = pkgs.llvmPackages_10.libllvm.override { debugVersion = debugVersion; };
  # Annoying.
  llvm = libllvm.out // { outputUnspecified = true; };

in
  stdenv.mkDerivation rec {
  pname = "euforia";
  version = "1.0";

  src =
    with builtins; filterSource
    (path: _:
    !elem (baseNameOf path) [ ".git" "result" "bin" ]) ./.;

  nativeBuildInputs = [
    cmake
    lit
    ninja
    outputCheck
  ];

  buildInputs = [
    # For some reason cmake really wants to link bz2 and I don't know why.
    bzip2
    boost17x
    z3
    llvm
    boolector
    gmp
    mathsat
  ];

  cmakeFlags = [
    "-DCMAKE_BUILD_TYPE=${if debugVersion then "Debug" else "Release"}"
    "-DLLVM_DIR=${libllvm.dev}/lib/cmake/llvm"
    "-DZ3_DIR=${z3}/lib/cmake/z3"
    "-DMATHSAT_DIR=${mathsat}"
    "-DBoolector_DIR=${boolector}"
    "-Dpropagate_const_DIR=${propagateConst}/lib/cmake/propagate_const"
    "-DImmer_DIR=${immer}/lib/cmake/Immer"
    "-Dfmt_DIR=${fmt}/lib/cmake/fmt"
    "-GNinja"
  ] ++ lib.optional sanitizer "-DCOMPILE_WITH_UBSAN=TRUE";

  doCheck = true;

  tags = pkgs.runCommand "euforia-tags" {
    buildInputs = [ universal-ctags ];
  }
  ''
    set -x
    mkdir -p $out
    ctags --c++-kinds=+pf --c-kinds=+p --fields=+imaSft --extras=+q -Rnu \
      ${libllvm.dev}/include \
      ${z3}/include \
      ${boolector}/include \
      ${propagateConst}/include \
      ${immer}/include \
      ${fmt}/include
    cp tags $out/
  '';

  meta = with lib; {
    description = "A model checker with uninterpreted functions abstraction";
    homepage = "https://github.com/dbueno/euforia";
    maintainers = [ denisbueno ];
  };
}
