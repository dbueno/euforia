extern void __VERIFIER_error() __attribute__ ((__noreturn__));
#define __VERIFIER_assert(c) if (!(c)) __VERIFIER_error();

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();



#define BUFFERSIZE 25
#define INPUT_LEN 30
#define TRUE 1
#define FALSE 0

void copy_it(int inputsize)
{
    char lbuf[BUFFERSIZE];
    int p = 0;
    char c, *d = &lbuf[0];
    char *ulimit = &lbuf[BUFFERSIZE-10];
    int quotation = FALSE;
    int rquote = FALSE;

    while(p++ < inputsize) {
        c = __VERIFIER_nondet_char();
        if ((c == '<') && (!quotation))
        {
            quotation = TRUE;
            ulimit--;
        }
        if ((c == '>') && (quotation))
        {
            quotation = FALSE;
            ulimit++;
            }
        if (c == '(' && !quotation && !rquote)
        {
            rquote = TRUE;
            // FIX: insert ulimit--; here
            }
        if (c == ')' && !quotation && rquote)
        {
            rquote = FALSE;
            ulimit++;
        }
        if (d < ulimit) {
            __VERIFIER_assert(d < lbuf + BUFFERSIZE);
            d++;
        }
    }
}

int main(int argc, char **argv) {
  int inputsize = __VERIFIER_nondet_int();
    copy_it(inputsize);
    return 0;
}
