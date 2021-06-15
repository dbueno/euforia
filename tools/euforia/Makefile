LIBDIR = $(shell pwd)/../..
include ../Makefile.common
SRCS = main.cpp

main.o: main.cpp

.PHONY: clean distclean
clean:
	rm -f *.o
	rm -f *.a

distclean: clean
	rm -rf .d


-include $(patsubst %,$(DEPDIR)/%.d,$(basename $(SRCS)))
