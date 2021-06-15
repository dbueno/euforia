
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
#define __VERIFIER_assert(c) if (!(c)) __VERIFIER_error();

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int(void);

int main() {
  int i = __VERIFIER_nondet_int();
  if (i != 0)
    return 0;
  do {
    __VERIFIER_assert(i < 7);
    i += 3;
  } while (i < 5);
  __VERIFIER_assert(i < 7);
  return 0;
}
