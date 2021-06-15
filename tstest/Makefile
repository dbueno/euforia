LIBDIR = ../../..
SRCS = main.cpp
SRCDIR = ../APICA/src
EXTRA_INCLUDE = -I$(SRCDIR)
LDFLAGS = -L$(LIBDIR)/llvm-dsa/install/lib -L$(LIBDIR)/z3/build

all: tstest

tstest: main.o $(SRCDIR)/libapica.a $(LIBDIR)/boolector/boolector/build/libboolector.a
	$(CXX) $(CXXFLAGS) $(LDFLAGS) $< -o $@ \
	    -Xlinker -rpath -Xlinker $(LIBDIR)/llvm-dsa/install/lib \
	    $(SRCDIR)/libapica.a $(LIBDIR)/boolector/boolector/build/libboolector.a $(LIBDIR)/boolector/lingeling/liblgl.a -lLLVM-3.7svn -lz3 -lpthread


$(SRCDIR)/libapica.a: force_look
	$(MAKE) -C $(SRCDIR)

force_look:
	@true

.PHONY: clean
clean:
	rm -f *.o
	rm -f tstest
	$(MAKE) -C $(SRCDIR) clean

include ../APICA/Makefile.common
-include $(patsubst %,$(DEPDIR)/%.d,$(basename $(SRCS)))
