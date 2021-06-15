#include <string.h>
#include <assert.h>
#include <stdio.h>

#define BUFFERSIZE 25
#define INPUT_LEN 30
#define TRUE 1
#define FALSE 0

void copy_it(const char *input)
{
    char lbuf[BUFFERSIZE];
    char c, *p = (char*)input, *d = &lbuf[0];
    char *ulimit = &lbuf[BUFFERSIZE-10];
    int quotation = FALSE;
    int rquote = FALSE;

    memset(lbuf, 0, BUFFERSIZE);

    while((c = *p++) != '\0') {
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
            assert(d < lbuf + BUFFERSIZE);
            *d++ = c;
        }
    }
//    if (rquote)
//        *d++ = ')';
//    if (quotation)
//        *d++ = '>';
}

int main(int argc, char **argv) {
    char input[INPUT_LEN];
    for (int i = 0; i < INPUT_LEN; i++) {
        input[i] = (char)getchar();
    }
    copy_it(input);
    return 0;
}
