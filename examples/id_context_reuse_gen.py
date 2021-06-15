#!/usr/bin/env python

# ./script 20


import sys
N = int(sys.argv[1])
V = 'a'
S = 100

print """#include "svcomp.h"

int find_at(unsigned length) {
  int i = 0;
  while (length-- != 0) {
    char c = __VERIFIER_nondet_char();
    if (c == '@')
      return i;
    ++i;  
  }
  return -1;
}
"""

print 'int main() {'
for i in xrange(N):
    print '  int a%d = find_at(%d);' % (i,S)
print '  __VERIFIER_assert(',
for i in xrange(N):
    if i>0:
        print '    ||',
    print '%d != a%d' % (S-1,i)
print '  );'
print '  return 0;\n}'
