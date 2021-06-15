#include "svcomp.h"

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

int main() {
  int a0 = find_at(100);
  int a1 = find_at(100);
  int a2 = find_at(100);
  int a3 = find_at(100);
  int a4 = find_at(100);
  __VERIFIER_assert( 99 != a0
    || 99 != a1
    || 99 != a2
    || 99 != a3
    || 99 != a4
  );
  return 0;
}
