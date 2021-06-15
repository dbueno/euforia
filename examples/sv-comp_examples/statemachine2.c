
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
#define __VERIFIER_assert(c) if (!(c)) __VERIFIER_error();

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();

int main(void) { 
    int tmp;
    int f = 1;
    int s = 1;

    while (1) {
        tmp = __VERIFIER_nondet_int();

        if (s == 1) goto begin;
        if (s == 2) goto two_a;
        if (s == 3) goto then_b;
        else goto accept;

begin:
        if (tmp == 'a') s = 2;
        continue;

two_a:
        if (tmp == 'a') s = 3;
        //if (f == 1) f = 2;
        continue;

then_b:
        if (tmp == 'b') s = 4;
        if (tmp) s = 1;
        if (f == 2) f = 3;
        continue;

accept:
        goto end;

}

end:
    __VERIFIER_assert(f == 3);
    return 0;

}
