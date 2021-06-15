with (import <nixpkgs> {});
# Use shell hook:
# - Tell me I'm in the euforia shell.
# - Make build dir.

let
  euforia = import ./default.nix;
  mkShell = pkgs.mkShell.override { stdenv = euforia.stdenv; };
in mkShell {
  inputsFrom = with pkgs; [ euforia ];
  buildInputs = [ creduce ctags ];
  srcDir = ./.;
  hardeningDisable = [ "all" ];
}
