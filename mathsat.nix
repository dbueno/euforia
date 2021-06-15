with import <nixpkgs> {};
#{ stdenv, fetchurl }:

let
  version = "5.6.5";
  name = "mathsat";
in stdenv.mkDerivation rec {
  inherit name version;
  
  src = fetchurl {
    url = "https://mathsat.fbk.eu/download.php?file=${name}-${version}-"
      + lib.optionalString stdenv.hostPlatform.isDarwin "darwin-libcxx-x86_64"
      + lib.optionalString stdenv.hostPlatform.isLinux "linux-x86_64"
      + ".tar.gz";
    sha256 =
      lib.optionalString stdenv.hostPlatform.isDarwin "bf13877df67e1a9529474644de2999ba3b5e314f82a8790138e4ddd5c5cd5bfa"
      + lib.optionalString stdenv.hostPlatform.isLinux "08kr8vv58brpbqhd3rdc44y8sf1s2wpklblc5myync7zq4sgydvf";
  };

  nativeBuildInputs = [ gmp ];

  inherit gmp;
  
  installPhase = ''
    mkdir $out
    cp -r . $out/
  '' + lib.optionalString stdenv.hostPlatform.isDarwin ''
    install_name_tool -id $out/lib/libmathsat.dylib $out/lib/libmathsat.dylib
    install_name_tool -change /usr/local/lib/libgmp.10.dylib $gmp/lib/libgmp.dylib $out/lib/libmathsat.dylib
    install_name_tool -change /usr/local/lib/libgmpxx.4.dylib $gmp/lib/libgmpxx.dylib $out/lib/libmathsat.dylib
  '' + lib.optionalString stdenv.hostPlatform.isLinux ''
  '';
}
