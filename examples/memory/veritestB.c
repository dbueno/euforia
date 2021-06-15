

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern char __VERIFIER_nondet_char();

 
int main() {
    char input[100];

    for (unsigned i = 0; i < 100; i++) {
        input[i] = __VERIFIER_nondet_char();
    }
    
    int counter = 0, values = 0;
    for (unsigned i = 0; i < 100; i++) {
        if (input[i] == 'B') {
            counter++;
            values += 2;
        }
    }
    if (counter == 2) __VERIFIER_error();

    return 0;
}
