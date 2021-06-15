/* From SLAM paper, Relative Completeness of Abstraction Refinement for Software Model Checking */
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();

int main() {
    int x = 0, y, z;
    y = __VERIFIER_nondet_int();

    while (x >= 0) {
        x = x + 1;
    }
    if (y == 25) {
        if (y != 25) {
            z = -1;
            while (z != 0) {
                z = z - 1;
            }
            __VERIFIER_error();
        }
    }
}
