#!/bin/sh


c_file=$1

docker run -v `pwd`:/benchmarks/ seahorn/seahorn sea fe -o /benchmarks/$c_file.bc /benchmarks/$c_file
docker run -v `pwd`:/benchmarks/ seahorn/seahorn sea horn --step=small -o /benchmarks/$c_file.small.smt2 /benchmarks/$c_file.bc
docker run -v `pwd`:/benchmarks/ seahorn/seahorn llvm-dis -o=/benchmarks/$c_file.ll /benchmarks/$c_file.bc
#docker run -v `pwd`:/benchmarks/ seahorn/seahorn sea smt -o /benchmarks/$c_file.smt2 /benchmarks/$c_file
docker run -v `pwd`:/benchmarks/ seahorn/seahorn seahorn --keep-shadows=true --horn-solve -horn-inter-proc -horn-sem-lvl=mem --horn-step=large -horn-cex-pass -horn-answer /benchmarks/$c_file.bc
echo 'unsat = safe'
echo 'sat = unsafe'
# docker run -v `pwd`:/benchmarks/ seahorn/seahorn sea pf --show-invars /benchmarks/rummer_safe.c


