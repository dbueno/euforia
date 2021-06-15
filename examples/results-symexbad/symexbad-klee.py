import sys

N = int(sys.argv[1])

print """
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>


int main(int argc, char **argv) {
  int a1;
  klee_make_symbolic(&a1, sizeof(a1), "a1");"""

for v in xrange(2, N+1):
    print "  int a%d = a%d+1;" % (v, v-1)

print ''

for v in reversed(xrange(2, N+1)):
    print """
  int b%d;
  klee_make_symbolic(&b%d, sizeof(b%d), "b%d");
  if (b%d) {
    a%d = a%d;
  }""" % (v-1, v-1, v-1, v-1, v-1, v-1, v)


print "  assert(a1 != a%d);" % N


print "}"

