extern void __VERIFIER_error(void) __attribute__ ((__noreturn__));
#define __VERIFIER_assert(c) if (!(c)) __VERIFIER_error()

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern long __VERIFIER_nondet_long(void);
extern unsigned long __VERIFIER_nondet_ulong(void);
extern void *__VERIFIER_nondet_pointer(void);

extern void __VERIFIER_assume(int);

extern void __VERIFIER_printf(const char *fmt, ...) __attribute__ ((format (printf, 1, 2)));

int f(int n) {
  int rec;
  if (n > 0) {
    int tmp = f(n-1);
    rec = tmp + 1;
  } else {
    rec = 1;
  }
  return rec;
}

int main() {
  int res;
  int x = __VERIFIER_nondet_int();
  if (x >= 0) {
    res = f(x);
    __VERIFIER_assert(res == x+1);
  }
}
