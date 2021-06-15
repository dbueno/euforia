#!/bin/bash

set -x
DEVNULL="/dev/stderr"

euforia="@CMAKE_BINARY_DIR@/bin/euforia"

gtimeout -k 1 15s $euforia bad.vmt >$DEVNULL 2>&1
if [ "$?" -eq "69" ]; then
  # interesting
  exit 0
else
  # not interesting
  exit 1
fi
