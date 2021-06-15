#include <stdio.h>

#include "smack.h"
//#include <assert.h>

#define N 2
 
int main(int argc, char **argv)
{
    int m, n, c, d, matrix[N][N], transpose[N][N];

#if N >= 2
    matrix[0][0] = getchar();
    matrix[0][1] = getchar();
    matrix[1][0] = getchar();
    matrix[1][1] = getchar();
#endif
#if N >= 3
    matrix[0][2] = getchar();
    matrix[1][2] = getchar();
    matrix[2][0] = getchar();
    matrix[2][1] = getchar();
    matrix[2][2] = getchar();
#endif
#if N >= 4
    matrix[0][3] = getchar();
    matrix[1][3] = getchar();
    matrix[2][3] = getchar();
    matrix[3][0] = getchar();
    matrix[3][1] = getchar();
    matrix[3][2] = getchar();
    matrix[3][3] = getchar();
#endif
 
   /* 
    for (c = 0; c < m; c++) {
        for (d = 0; d < n; d++) {
            matrix[c][d] = getchar();
            transpose[c][d] = 0;
        }
    }
    */
    
    for (c = 0; c < N; c++) {
        for (d = 0; d < N; d++) {
            transpose[d][c] = matrix[c][d];
        }
    }
 
    printf("Transpose of entered matrix :-\n");
    assert(matrix[0][1] == transpose[1][0]);
#if 0
 
    for (c = 0; c < m; c++) {
        for (d = 0; d < n; d++) {
            printf("%d\t",transpose[c][d]);
            //__SMACK_assert(matrix[c][d] == transpose[d][c]);
            assert(matrix[c][d] == transpose[d][c]);
        }
        printf("\n");
    }
#endif
 
    return 0;
}
