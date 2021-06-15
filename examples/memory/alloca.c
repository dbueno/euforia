
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
#define __VERIFIER_assert(c) if (!(c)) __VERIFIER_error();

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern unsigned long __VERIFIER_nondet_ulong(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();

void f(unsigned char* p) {
  *p = 1;
}

int main(int argc, char** argv) {
  unsigned char data = 0;

  f(&data);
  __VERIFIER_assert(data == (unsigned char)0);

  return 0;
}
