#!/usr/bin/env bash

CBMC=cbmc

set -x

EXTRA_CFLAGS='-Wno-switch -Wno-unused -Wno-parentheses-equality -Wno-newline-eof'
CLANG="/opt/llvm-5.0.0/bin/clang"
INCLUDEPATH="$HOME/work/euforia/examples"
DEVNULL="/dev/stderr"

BUGGY="$HOME/work/euforia/xcode/build-Debug/bin/EUForia-3.2"

gcc -o /dev/null -std=c99 -pedantic -Wall -Werror $EXTRA_CFLAGS -m32 -I$INCLUDEPATH -c bad.c >$DEVNULL 2>&1 &&\
$CLANG -emit-llvm -std=c99 -pedantic -Wall -Werror $EXTRA_CFLAGS -m32 -I$INCLUDEPATH -c bad.c -o /dev/null >$DEVNULL 2>&1 &&\
$CLANG -emit-llvm -m32 $EXTRA_CFLAGS -I$INCLUDEPATH -c bad.c -o bad.o >$DEVNULL 2>&1 || exit 1

function killeverything {
  kill -9 $cbmcpid
  kill -9 $euforiapid
}

$CBMC bad.c >& cbmc.out &
cbmcpid=$!
$BUGGY bad.o >& euforia.out &
euforiapid=$!
trap killeverything SIGTERM
wait

OLDEXIT=1
if grep 'VERIFICATION FAILED' cbmc.out >& /dev/null; then
  OLDEXIT=20
elif grep 'VERIFICATION SUCCESSFUL' cbmc.out >& /dev/null; then
  OLDEXIT=10
fi

NEWEXIT=1
if grep '^false(unreach' euforia.out >& /dev/null; then
  NEWEXIT=20
elif grep '^true(unreach' euforia.out >& /dev/null; then
  NEWEXIT=10
fi

if [ "$OLDEXIT" -eq "10" ] || [ "$OLDEXIT" -eq "20" ]; then
    if [ "$NEWEXIT" -eq "10" ] || [ "$NEWEXIT" -eq "20" ]; then
        if [ "$OLDEXIT" -ne "$NEWEXIT" ]; then
          exit 0
        fi
    fi
fi
exit 1
