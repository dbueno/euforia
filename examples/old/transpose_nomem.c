
#include <stdio.h>

#include "smack.h"
//#include <assert.h>

#define N 4
#define M 4

 
int main(int argc, char **argv)
{
    int a11, a12, a21, a22;
    int b11, b12, b21, b22;

    a11 = getchar();
    a12 = getchar();
    a21 = getchar();
    a22 = getchar();
    b11 = b12 = b21 = b22 = 0;


    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2; j++) {
            if (i == 0 && j == 0) {
                b11 = a11;
                b21 = a12;
                b12 = a21;
                b22 = a22;
            }
        }
    }

    assert(b12 == a21);
/*    __SMACK_assert(b21 == a12);
    __SMACK_assert(b11 == a11);
    __SMACK_assert(b22 == a22);
  */  
    return 0;
}
