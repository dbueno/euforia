{ python38, fetchFromGitHub }:
python38.pkgs.buildPythonPackage rec {
  pname = "OutputCheck";
  version = "eab62a5dd5129f6a4ebfbe4bbe41d35611f7c48d";
  src = fetchFromGitHub {
    owner = "stp";
    repo = "OutputCheck";
    rev = "${version}";
    sha256 = "0pbqnamnixx7gagcfw9l9jvw1rafkqnv9rvg25zk1sps76b4ngnh";
  };
  doCheck = false;
  patchPhase = ''
      substituteInPlace setup.py --replace "version.get_git_version()" \
        "'${version}'"
  '';
}
