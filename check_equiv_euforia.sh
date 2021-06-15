#!/bin/bash


# similar to creduce'ing something but with reverse failure mode and customizable argument
EXTRA_CFLAGS='-Wno-switch -Wno-unused -Wno-parentheses-equality -Wno-newline-eof'

DIR=`mktemp -d`
mkdir -p "$DIR"
BAD="$1"
cp "$1" "$DIR/"
cd $DIR

$HOME/work/euforia/xcode/bin/EUForia_2_golden --true-exit-status=10 --false-exit-status=20 --silent $BAD >/dev/null 2>&1 & OLDPID=$!
$HOME/work/euforia/xcode/bin/EUForia3 --true-exit-status=10 --false-exit-status=20 --out-dir="$DIR" --silent $BAD >/dev/null 2>&1 & NEWPID=$!
wait $OLDPID
OLDEXIT="$?"
wait $NEWPID
NEWEXIT="$?"
echo 'OLDEXIT:' $OLDEXIT
echo 'NEWEXIT:' $NEWEXIT
if [ "$OLDEXIT" -eq "10" ] || [ "$OLDEXIT" -eq "20" ]; then
    if [ "$NEWEXIT" -eq "10" ] || [ "$NEWEXIT" -eq "20" ]; then
        if [ "$OLDEXIT" -ne "$NEWEXIT" ]; then
          exit 1 # error when exit codes are different
        fi
    fi
fi

exit 0
