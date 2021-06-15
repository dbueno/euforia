#!/usr/bin/env bash

# 10 is true-exit
# 20 is false-exit
# testing.txt specifies whether the result should be 10 or 20

# if test -n "$1"; then
#     EUFORIA="$1"
#     shift
# else
    EUFORIA=@CMAKE_BINARY_DIR@/bin/euforia
# fi
EXAMPLE_DIR=@EUFORIA_EXAMPLES@
if [[ "$EXAMPLE_DIR" == @E* ]]; then
  EXAMPLE_DIR=../../examples
fi
TESTS=$EXAMPLE_DIR/testing.txt
#TIME=${TIME:-'gtime -p'}

if ! test -x "$EUFORIA"; then
    echo "Could not find $EUFORIA"
    exit 1
fi
EUFORIA="$EUFORIA $@"
echo "Testing '$EUFORIA'"

OUTFILE=`mktemp`

#awk '{print $2}' "$TESTS" | xargs -n 1 make -C $EXAMPLE_DIR

printf "Output of last test is in %s\n" "$OUTFILE"

#printf "Running concrete checks\n"
#cd $EXAMPLE_DIR
#cat "$TESTS" | \
#while read -ra RECORD; do
#    printf "Running %s\n" "${RECORD[1]}"
#    $EUFORIA --no-abstraction --verify-invariant --true-exit-status=10 --false-exit-status=20 "$@" "${RECORD[1]}" >&"$OUTFILE"
#    RET=$?
#    if [ "$RET" != "${RECORD[0]}" ]; then
#        echo "ERROR IN TESTCASE: ${RECORD[1]}"
#        echo "additional args: $@"
#        echo "expected: ${RECORD[0]}"
#        echo "actual: $RET"
#        echo "output:"
#        echo "Output is in $OUTFILE:"
#        echo "***********************************************************************"
#        head -10 "$OUTFILE"
#        WC=$(wc -l $OUTFILE| cut -d' ' -f6)
#        echo ""
#        echo "[ ... $((WC  - 20)) lines omitted ... ]"
#        echo ""
#        tail -10 "$OUTFILE"
#        exit 1
#    fi
#done

printf "Running abstract checks\n"
cd $EXAMPLE_DIR
cat "$TESTS" | sed '/^#/d' | \
while read -ra RECORD; do
    printf "Running '%s'\n" "$EUFORIA --verify-invariant --true-exit-status=10 --false-exit-status=20 \"${RECORD[1]}\""
    $EUFORIA --verify-invariant --true-exit-status=10 --false-exit-status=20 "${RECORD[1]}" >&"$OUTFILE"
    RET=$?
    if [ "$RET" != "${RECORD[0]}" ]; then
        echo "ERROR IN TESTCASE: ${RECORD[1]}"
        echo "additional args: $@"
        echo "expected: ${RECORD[0]}"
        echo "actual: $RET"
        echo "output:"
        echo "Output is in $OUTFILE:"
        echo "***********************************************************************"
        head -10 "$OUTFILE"
        WC=$(wc -l $OUTFILE| cut -d' ' -f6)
        echo ""
        echo "[ ... $((WC  - 20)) lines omitted ... ]"
        echo ""
        tail -10 "$OUTFILE"
        exit 1
    fi
done

rm -f "$OUTFILE"
#parallel -j1 ./bin/EUForia --true-exit-status=0 --false-exit-status=10 --silent ../examples/{2} < ../examples/testing.txt
