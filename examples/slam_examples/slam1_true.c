extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();


void foo() {
    int x, y, z, w;

    w = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();

    do {
        z = 0;
        x = y;
        if (w) {
            x++;
            z = 1;
        }
    } while (x != y);
    if (z) __VERIFIER_error();
}

int main() {
    foo();
    return 0;
}

