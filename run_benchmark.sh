#!/opt/brew/bin/bash

# Usually I make problem files with 'ls -1 c/bin/<some-glob>*oc'

# File that has a list of problems rooted at c/bin in SV-COMP
PROBLEMS="$1"
DIR="$HOME/work/sv-benchmarks/c/bin"
EUFORIA="./bin/EUForia_xcode"

usage() {
    echo "./run_benchmark Problems.txt [result-dir]"
}

if ! test -f "$PROBLEMS"; then
    echo "Could not find problems file: " "$PROBLEMS"
    usage
    exit 1
fi

RESULT_DIR="$2"
if test -z "$RESULT_DIR"; then
    RESULT_DIR="results"
fi


if ! test -d "$DIR"; then
    echo "Benchmarks not found"
    echo "Looked for: $DIR"
    usage
    exit 1
fi

ulimit -m 2500000
ulimit -v 2500000

parallel -j2 --files --results $RESULT_DIR --timeout 900 \
    time -p "$EUFORIA" --out-dir "/tmp/`basename $PROBLEMS`" $HOME/work/sv-benchmarks/c/bin/{} < "$PROBLEMS" 
