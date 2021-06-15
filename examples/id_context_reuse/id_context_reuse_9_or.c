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
  int a5 = find_at(100);
  int a6 = find_at(100);
  int a7 = find_at(100);
  int a8 = find_at(100);
  __VERIFIER_assert( 99 != a0
    || 99 != a1
    || 99 != a2
    || 99 != a3
    || 99 != a4
    || 99 != a5
    || 99 != a6
    || 99 != a7
    || 99 != a8
  );
  return 0;
}
