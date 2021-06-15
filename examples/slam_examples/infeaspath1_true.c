/* From SLAM paper, Generating Abstract Explanations of Spurious Counterxamples in C Programs */
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();

int main() {
    int a, b, c;
    a = __VERIFIER_nondet_int();
    b = __VERIFIER_nondet_int();
    c = __VERIFIER_nondet_int();

    if (b>0) {
        c = 2*b;
        a = b;
        a = a-1;
        if (a<b) {
            if (a==c) {
                __VERIFIER_error();
            }
        }
    }

    return 0;
}
