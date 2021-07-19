# To adapt a legacy nix to flakes
# From: https://nixos.wiki/wiki/Flakes
let
  lock = builtins.fromJSON (builtins.readFile ./flake.lock);
  flake-compat-src = fetchTarball {
    url = "https://github.com/edolstra/flake-compat/archive/${lock.nodes.flake-compat.locked.rev}.tar.gz";
    sha256 = lock.nodes.flake-compat.locked.narHash;
  };
  flake = flake-compat { src = ./.; };
in 
  flake.defaultNix
