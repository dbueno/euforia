{ stdenv, fetchFromGitHub, cmake }:
stdenv.mkDerivation {
  pname = "fmtlib";
  version = "7.3.1";
  src = fetchFromGitHub {
    owner = "fmtlib";
    repo = "fmt";
    rev = "7bdf0628b1276379886c7f6dda2cef2b3b374f0b";
    sha256 = "08hyv73qp2ndbs0isk8pspsphdzz5qh8czl3wgyxy3mmif9xdg29";
  };
  buildInputs = [ cmake ];
  cmakeFlags = [ "-DCMAKE_POSITION_INDEPENDENT_CODE=TRUE" ];
  doCheck = true;
  checkTarget = "test";
}
