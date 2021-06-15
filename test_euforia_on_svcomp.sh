#!/usr/bin/env bash

NUM_CORES=6
SVCOMP_DIR=$HOME/work/sv-benchmarks

CMD="parallel --jobs /tmp/svcomp_jobs.txt -j$NUM_CORES ./check_sv-comp_unreach.sh --verify-invariant"

$CMD {} ::: $SVCOMP_DIR/c/bin/eca-rers2012/Problem{01,02,10}_label{1,2}*oc $SVCOMP_DIR/c/bin/ssh-simplified/*oc $SVCOMP_DIR/c/bin/ntdrivers-simplified/*oc $SVCOMP_DIR/c/bin/systemc/{pc_sfifo,token_ring,transmitter,toy}*oc
#$CMD {} ::: $SVCOMP_DIR/c/bin/ntdrivers-simplified/*oc
