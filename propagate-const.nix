{ stdenv, fetchFromGitHub, cmake }:
stdenv.mkDerivation {
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
}
