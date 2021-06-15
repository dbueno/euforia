#include "svcomp.h"

#define SWAP_XOR(a, b) (((a) ^= (b)), ((b) ^= (a)), ((a) ^= (b)))
#define SWAP_ADD(a, b) ((&(a) == &(b)) || \
                    (((a) -= (b)), ((b) += (a)), ((a) = (b) - (a))))

#define MOD 1000

long long fast_power(long long base, long long power) {
    long long result = 1;
    while(power > 0) {

        if(power % 2 == 1) { // Can also use (power & 1) to make code even faster
            result = (result*base) % MOD;
        }
        base = (base * base) % MOD;
        power = power / 2; // Can also use power >>= 1; to make code even faster
    }
    return result;
}


unsigned gcd(unsigned a, unsigned b) {
  while (b != 0) {
    unsigned t = b;
    b = a % b;
    a = t;
  }
  return a;
}


unsigned gcd2(unsigned a, unsigned b) {
  if (a % 2) {
    return gcd(a, b);
  } else {
    return gcd(b, 116);
  }
}


#if 0
int foo(int x) {
  int y = __VERIFIER_nondet_int();
  __VERIFIER_assume(y<100);
  if (conf & MAGIC) {
    x = y;
    if (conf & MAGIC2) {
      y = y+z;
    }

    if (conf-2 & MAGIC3 == 0) {
      x=x-1;
    }
  }
  return x;
}
#endif

#define BUFSZ 25
void copy_it(int inputsize) {
  int p = 0;
  char c, d = 0;
  char ulimit = BUFSZ-10;
  int quotation = 0;
  int rquote = 0;

  while (p++ < inputsize) {
    c = __VERIFIER_nondet_char(); /* read from 'p' */
    if (c == '\0') break;

    if ((c == '<') && (!quotation)) {
      quotation = 1;
      ulimit--;
    }
    if ((c == '>') && (quotation)) {
      quotation = 0;
      ulimit++;
    }
    if (c == '(' && !quotation && !rquote) {
      rquote = 1;
      // FIX: insert ulimit--; here
    }
    if (c == ')' && !quotation && rquote) {
        rquote = 0;
        ulimit++;
    }
    if (d < ulimit) {
        __VERIFIER_assert(d < BUFSZ);
        /* *d++ = c originally. it was a write to a buffer. */
        d++;
    }
  }
}

int main() {
  copy_it(6);
  return 0;
}
