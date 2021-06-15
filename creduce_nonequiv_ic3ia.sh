#!/usr/bin/env bash

function killeverything {
  kill -9 $pid1
  kill -9 $pid2
}

set -x

EXTRA_CFLAGS='-Wno-switch -Wno-unused -Wno-parentheses-equality -Wno-newline-eof'
CLANG="/opt/llvm-5.0.0-c++17/bin/clang"

ic3ia=~/work/vmcai18/ic3ia/build/ic3ia
stable_euforia=/opt/euforia/bin/EUForia-3.3
euforia=~/work/euforia/xcode/build-Debug/bin/EUForia-3.3

# compile file to llvm object
$CLANG -emit-llvm -std=c99 -pedantic -Wall -Werror $EXTRA_CFLAGS -m32 -c bad.c -o bad.o

# run stable euforia to dump vmt
rm -f bad.vmt
$stable_euforia --inline-threshold=9999999 --no-check --no-abstraction --dump-vmt bad.vmt bad.o >& /dev/null

# run ic3ia
$ic3ia bad.vmt >& ic3ia.out &
pid1=$!

# run euforia
$euforia bad.o >& euforia.out &
pid2=$!

trap killeverything SIGTERM
wait

# if they differ, retrun 0
exit1=0
if grep '^unsafe' ic3ia.out >& /dev/null; then
  exit1=20
elif grep '^safe' ic3ia.out >& /dev/null; then
  exit1=10
fi

exit2=0
if grep '^false(unreach' euforia.out >& /dev/null; then
  exit2=20
elif grep '^true(unreach' euforia.out >& /dev/null; then
  exit2=10
fi

# both checkers must terminate successfully
if [ "$exit1" -gt "0" ] && [ "$exit2" -gt "0" ]; then
  # but differ on their answer
  if [ "$exit1" -ne "$exit2" ]; then
    exit 0
  fi
fi
exit 1
