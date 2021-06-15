#!/bin/bash

set -x

EXTRA_CFLAGS='-Wno-switch -Wno-unused -Wno-parentheses-equality -Wno-newline-eof'
CLANG="/opt/llvm-5.0.0-with-gcc-7/bin/clang"
GOLDEN="$HOME/work/euforia/xcode/build/bin/EUForia3 -s --inline-threshold=300"
#GOLDEN="$HOME/work/euforia/xcode/bin/EUForia_2_golden"
BUGGY="$HOME/work/euforia/xcode/build/bin/EUForia3 -s"
#BUGGY="$HOME/work/euforia/xcode/bin/EUForia3"

gcc -o /dev/null -std=c99 -pedantic -Wall -Werror $EXTRA_CFLAGS -m32 -c bad.c >/dev/null 2>&1 &&\
$CLANG -emit-llvm -std=c99 -pedantic -Wall -Werror $EXTRA_CFLAGS -m32 -c bad.c -o /dev/null >/dev/null 2>&1 &&\
$CLANG -emit-llvm $EXTRA_CFLAGS -m32 -c bad.c -o bad.o >/dev/null 2>&1

$GOLDEN --true-exit-status=10 --false-exit-status=20 --silent bad.o >/dev/null 2>&1 & OLDPID=$!
$BUGGY --true-exit-status=10 --false-exit-status=20 --silent bad.o >/dev/null 2>&1 & NEWPID=$!

echo "waiting"
wait $OLDPID
OLDEXIT="$?"
wait $NEWPID
NEWEXIT="$?"
if [ "$OLDEXIT" -eq "10" ] || [ "$OLDEXIT" -eq "20" ]; then
    if [ "$NEWEXIT" -eq "10" ] || [ "$NEWEXIT" -eq "20" ]; then
        if [ "$OLDEXIT" -ne "$NEWEXIT" ]; then
          exit 0
        fi
    fi
fi
exit 1
