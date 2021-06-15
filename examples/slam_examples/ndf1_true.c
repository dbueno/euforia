/* From SLAM paper, Refining Approximations in Software Predicate Abstraction */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();


int main() {
    int x, y, z;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    z = __VERIFIER_nondet_int();

    if (x<y) {
        if (y<z) {
            if (!(x<z)) {
                __VERIFIER_error();
            }
        }
    }

    return 0;
}

