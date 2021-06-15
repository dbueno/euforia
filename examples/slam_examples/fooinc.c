
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
#define __VERIFIER_assert(c) if (!(c)) __VERIFIER_error();

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();

int inc(int x) {
  x = x+1;
  return x;
}

void foo(int a) {
  int b, c;
  b = inc(a);
  c = inc(b);

  __VERIFIER_assert(a != 2 || c == 4);
  return;
}
