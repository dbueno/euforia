Overview
========

Nix Flakes
----------

Just run

::

    nixFlakes run . -- <vmt-file>

Nix Build (Without Flakes)
--------------------------

The file ``default.nix`` contains a complete build description that
works with the `Nix package
manager <https://nixos.org/guides/install-nix.html>`__.

After cloning the repo, you can do:

::

    nix-build .

and after the build completes, you can run euforia like so:

::

   ./result/bin/euforia <vmt-file>

You can find some example VMT files in ``./examples``.

General advice
--------------

If you like, ``setup.sh`` can give you a general idea of how to build euforia,
but it might be out of sync with the nix build. The nix build is in
``euforia.nix``.
