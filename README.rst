Overview
========

Nix Flakes
----------

Just run

::

    nixFlakes run . -- -h

Nix Build Without Flakes
------------------------

The file ``default.nix`` contains a complete build description that
works with the `Nix package
manager <https://nixos.org/guides/install-nix.html>`__.

After cloning the repo, you can do:

::

   nix-build -E "with import <nixpkgs> {}; callPackage ./default.nix {}"

and after the build completes, you can run euforia.

::

   ./result/bin/euforia <vmt-file>

You can find some example VMT files in ``./examples``.

General advice
--------------

If you like, setup.sh can give you a general idea of how to build
euforia, but it might be out of sync with the nix build.
