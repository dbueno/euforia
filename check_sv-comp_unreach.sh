#!/bin/bash

if test -z "$1"; then
  echo "Need filename"
  exit 1
fi

ARGS=""
while [ "$#" -gt "1" ]; do
  ARGS="$1 $ARGS"
  shift
done

euforia="@CMAKE_BINARY_DIR@/bin/euforia"
clang="@LLVM_DIR@/../../../bin/clang"
benchmark_filename="$1"

if [[ $file =~ \.c$ ]]; then
  output_filename=$(basename $1).bc
  $clang -c -emit-llvm -o /tmp/$output_filename
  benchmark_filename=$output_filename
fi

# make directory so we can send all output there
#outdir=`mktemp -d`
#outfile="$outdir/$(basename $1 .c).bc"
#benchmark_filename="$(basename $1)"
#cp "$1" "$outdir/"
#cd "$outdir"

EXPECT_TRUE="$(echo "$benchmark_filename" | grep -o '_true-unreach-call')"
EXPECT_FALSE="$(echo "$benchmark_filename" | grep -o '_false-unreach-call')"
if [ -z "$EXPECT_TRUE" ] && [ -z "$EXPECT_FALSE" ]; then
    echo "error: expected exit status not found in filename:" $benchmark_filename
    exit 1
fi
if [ -n "$EXPECT_TRUE" ] && [ -n "$EXPECT_FALSE" ]; then
    echo "error: double expected status:" $benchmark_filename
    exit 1
fi

#extra_cflags='-Wno-switch -Wno-unused -Wno-parentheses-equality -Wno-newline-eof'
#$clang $extra_cflags -c -emit-llvm -m32 -o "$outfile" "$1" || exit 1

#$euforia --no-abstraction --true-exit-status=10 --false-exit-status=20 --out-dir="$outdir" --silent $ARGS "$outfile" >/dev/null 2>&1
$euforia --true-exit-status=10 --false-exit-status=20 --silent $ARGS "$benchmark_filename" >/dev/null 2>&1

NEWEXIT="$?"
echo $benchmark_filename 'EXIT:' $NEWEXIT
if [ "$NEWEXIT" -eq "10" ] && [ -n "$EXPECT_FALSE" ]; then
  echo "Output is in $outdir" 1>&2
  exit 1
elif [ "$NEWEXIT" -eq "20" ] && [ -n "$EXPECT_TRUE" ]; then
  echo "Output is in $outdir" 1>&2
  exit 1
elif [ "$NEWEXIT" -ne "10" ] && [ "$NEWEXIT" -ne "20" ]; then
  echo "Output is in $outdir" 1>&2
  echo "Bad exit code"
  exit 1
fi

test -d "$outdir" && rm -r "$outdir"
