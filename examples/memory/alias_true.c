#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

int main(int argc, char **argv)
{
    int X[1], Y[1];
    int *p, *q;

    if (getchar()) {
        p = X;
        q = Y;
    } else {
        p = Y;
        q = X;
    }

    *p = getchar();
    *q = *p+1;

    /* property should hold */
    assert(X[0] != Y[0]);
}
