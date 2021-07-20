{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };
  outputs = { self, nixpkgs, flake-utils, flake-compat }:
  let
    overlay = (final: prev: {
      euforiaPackages = final.lib.makeScope final.newScope (self: with self; {
        immer = callPackage ./immer.nix {};
        fmt = callPackage ./fmtlib.nix {};
        z3 = callPackage ./z3.nix {};
        mathsat = callPackage ./mathsat.nix {};
        outputCheck = callPackage ./outputcheck.nix {};
        propagateConst = callPackage ./propagate-const.nix {};
        euforia = callPackage ./euforia.nix { inherit self; };
      });
    });
  in
  {
    inherit overlay;
  } //
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { overlays = [ overlay ]; inherit system; };
      in {
        packages = pkgs.euforiaPackages;
        defaultPackage = pkgs.euforiaPackages.euforia;
        devShell =
          let
            euforiaDev = pkgs.euforiaPackages.euforia.override { debugVersion = true; };
          in
          pkgs.mkShell {
            inputsFrom = [ euforiaDev ];
            packages = with pkgs; [ creduce universal-ctags ];
            inherit (euforiaDev) cmakeFlags;
            hardeningDisable = [ "all" ];
            TAGS = "${euforiaDev.tags}/tags";
          };
        });
}
