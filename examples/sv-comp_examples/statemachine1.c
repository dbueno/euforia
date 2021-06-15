
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();
int main(void) 
{ 
    int f = 0;
    int tmp;

    while (1) {
        if (f % 2 != 0) goto ERROR;
        tmp = __VERIFIER_nondet_int();

        if (tmp)
            f += 2;
        else
            f -= 2;

    }
    return 0;

ERROR:
    __VERIFIER_error();
}
