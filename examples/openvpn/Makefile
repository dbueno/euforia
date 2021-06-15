CC = clang
SMACK_PATH = $(HOME)/work/smack
SMACKGEN = $(SMACK_PATH)/bin/smackgen.py
CFLAGS = -g -emit-llvm -m32 -O0 -I$(SMACK_PATH)/install/share/smack/include 
BPL = openvpn_bpl.py 

%_bpl.py: %.bc
	PATH="$(SMACK_PATH)/install/bin:$(PATH)" $(SMACKGEN) $^ -o $@

%.bc: %.c
	$(CC) $(CFLAGS) -c -o $@ $^

all: $(BPL)

clean:
	rm -f *.o *_bpl.py
