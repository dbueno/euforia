{ stdenv, fetchFromGitHub, cmake }:
stdenv.mkDerivation rec {
  pname = "immer";
  version = "v0.6.2-1";
  src = fetchFromGitHub {
    owner = "dbueno";
    repo = "immer";
    rev = "${version}";
    sha256 = "0d1qyckcp0wf1vl69ma6mf1862mxa8b5zgbz4rdgibaqf0yl97p7";
  };
  nativeBuildInputs = [ cmake ];
  dontBuild = true;
  patchPhase = ''
    rm BUILD
  '';
}

