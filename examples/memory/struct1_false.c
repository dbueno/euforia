
extern void __VERIFIER_error(void) __attribute__ ((__noreturn__));
#define __VERIFIER_assert(c) if (!(c)) __VERIFIER_error();

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern long __VERIFIER_nondet_long(void);
extern unsigned long __VERIFIER_nondet_ulong(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int(void);


struct foo {
    int a;
    char b;
};


struct foo fglobal;

int main(void) {


    fglobal.a = __VERIFIER_nondet_int();
    fglobal.b = __VERIFIER_nondet_char();

    if (fglobal.b < 5)
        __VERIFIER_error();

    return 0;

}
