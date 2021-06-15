LEVEL ?= .
LLVM_DIR = /opt/clang+llvm-10.0.0-x86_64-apple-darwin
CC = $(LLVM_DIR)/bin/clang
LLVM_DIS = $(LLVM_DIR)/bin/llvm-dis
LLVM2VMT = $(shell pwd)/../../llvm2vmt/code/euforia/build/Release/bin/VMT_Standalone-0.1
# to use regular clang, just do make CC=clang
CFLAGS = -emit-llvm -Wall -O0 -std=c99 -pedantic -Wno-switch -Wno-unused -Wno-parentheses-equality -Wno-newline-eof
LDFLAGS = -Wall -O0 -std=c99 -pedantic -Wno-switch -Wno-unused -Wno-parentheses-equality -Wno-newline-eof

BC ?=  loopy_false.bc \
      loopy2_false.bc \
      loopy3_false.bc \
      loopy_true.bc \
      statemachine1_false.bc \
      statemachine1_true.bc \
      loopint_true.bc \
      oddeven_true.bc \
      id_context_reuse_2_or.bc \
      id_context_reuse_3_or.bc \
      id_context_reuse_4_or.bc \
      id_context_reuse_5_or.bc \
      id_context_reuse_6_or.bc \
      id_context_reuse_7_or.bc \
      id_context_reuse_8_or.bc \
      id_context_reuse_9_or.bc \
      id_context_reuse_10_or.bc \
      id_context_reuse_11_or.bc \
      id_context_reuse_12_or.bc \
      id_context_reuse_13_or.bc \
      id_context_reuse_14_or.bc \
      id_context_reuse_15_or.bc \
      switch_true.bc \
      switch_small_true.bc


all: $(BC)

%.exe: %.bc svcomp.bc
	$(CC) $(LDFLAGS) -o $@ $^

%.bc: %.c svcomp.h
	$(CC) $(CFLAGS) -c -o $@ $<
%.bc: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

%.ll: %.bc
	$(LLVM_DIS) $^

%.vmt: %.bc
	$(LLVM2VMT) --dump-vmt=$@ $<

clean:
	rm -f *.bc $(BPL)
