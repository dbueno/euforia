{ ninja, cmake, boost17x, gmp, lit, fetchFromGitHub, git, pkgs, stdenv
, bzip2, boolector
, lib, python38
, debugVersion ? false
}:
let
  denisbueno = "Denis Bueno <dbueno@gmail.com>";
  libllvm = pkgs.llvmPackages_10.libllvm.override { debugVersion = debugVersion; };
  # Annoying.
  llvm = libllvm.out // { outputUnspecified = true; };

  outputCheck = python38.pkgs.buildPythonPackage rec {
    pname = "OutputCheck";
    version = "eab62a5dd5129f6a4ebfbe4bbe41d35611f7c48d";
    src = fetchFromGitHub {
      owner = "stp";
      repo = "OutputCheck";
      rev = "eab62a5dd5129f6a4ebfbe4bbe41d35611f7c48d";
      sha256 = "0pbqnamnixx7gagcfw9l9jvw1rafkqnv9rvg25zk1sps76b4ngnh";
    };
    doCheck = false;
    patchPhase = ''
      substituteInPlace setup.py --replace "version.get_git_version()" \
        "'${version}'"
    '';
  };

in
  stdenv.mkDerivation rec {
  pname = "euforia";
  version = "1.0";

  src =
    with builtins; filterSource
    (path: _:
    !elem (baseNameOf path) [ ".git" "result" "bin" ]) ./.;

  mathsat = import ./mathsat.nix;

  z3 = pkgs.z3.overrideAttrs (attr: with attr; rec {
    version = "4.8.7";
    src = fetchFromGitHub {
      owner  = "Z3Prover";
      repo   = pname;
      rev    = "z3-${version}";
      sha256 = "0hprcdwhhyjigmhhk6514m71bnmvqci9r8gglrqilgx424r6ff7q";
    };
  });

  propagateConst = stdenv.mkDerivation {
    pname = "propagate_const";
    version = "1.0.0";
    src = fetchFromGitHub {
      owner = "jbcoe";
      repo = "propagate_const";
      rev = "master";
      sha256 = "0gpfp8z7fvzdk4iyxb4zk6brdy5iy47wvx7w72i1g19rxlclr18g";
    };
    nativeBuildInputs = [ cmake ];
    cmakeFlags = [
      "-DBUILD_TESTING=OFF"
      "-DENABLE_SANITIZERS=OFF"
    ];
  };
  
  fmt = stdenv.mkDerivation {
    pname = "fmtlib";
    version = "5.0.0";
    src = fetchFromGitHub {
      owner = "fmtlib";
      repo = "fmt";
      rev = "5386f1df";
      sha256 = "00hsfax6x7kc0dfi4i3b8kd9bcs4na0dr2k1jn7ga5yq4gpkdg6p";
    };
    buildInputs = [ cmake ];
    cmakeFlags = [ "-DCMAKE_POSITION_INDEPENDENT_CODE=TRUE" ];
    doCheck = true;
    checkTarget = "test";
  };

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
    "-DZ3_DIR=${z3.lib}"
    "-DMATHSAT_DIR=${mathsat}"
    "-DBOOLECTOR_DIR=${boolector}"
    "-Dpropagate_const_DIR=${propagateConst}/lib/cmake/propagate_const"
    "-Dfmt_DIR=${fmt}/lib/cmake/fmt"
    "-GNinja"
  ];

  doCheck = true;

  meta = with lib; {
    description = "A model checker with uninterpreted functions abstraction";
    homepage = "https://github.com/dbueno/euforia";
    maintainers = [ denisbueno ];
  };
}
