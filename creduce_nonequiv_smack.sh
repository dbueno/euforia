#!/usr/bin/env bash

smack_dir=$HOME/work/smack

source $smack_dir/smack.env

EXTRA_CFLAGS='-Wno-switch -Wno-unused -Wno-parentheses-equality -Wno-newline-eof'
CLANG="/opt/llvm-5.0.0-c++17/bin/clang"

BUGGY="/opt/euforia/bin/EUForia-3.3"

gcc -o /dev/null -std=c99 -pedantic -Wall -Werror $EXTRA_CFLAGS -m32 -c bad.c >/dev/null 2>&1 &&\
$CLANG -emit-llvm -std=c99 -pedantic -Wall -Werror $EXTRA_CFLAGS -m32 -c bad.c -o /dev/null >/dev/null 2>&1 &&\
$CLANG -emit-llvm $EXTRA_CFLAGS -m32 -c bad.c -o bad.o >/dev/null 2>&1 || exit 1

function killeverything {
  kill -9 $smackpid
  kill -9 $buggypid
}


smack --verifier=svcomp --unroll=2 bad.c >& smack.out &
smackpid=$!
$BUGGY bad.o >& euforia.out &
buggypid=$!
trap killeverything SIGTERM
wait

OLDEXIT=1
if grep 'SMACK found an error' smack.out >& /dev/null; then
  OLDEXIT=20
elif grep 'SMACK found no errors' smack.out >& /dev/null; then
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
