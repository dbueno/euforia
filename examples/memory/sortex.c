#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

//#define USE_SWAPFUN 1

#define LOCS_ORDERED 1
//#define LOC_I_MOVED
//#define LOC_J_MOVED
//#define OTHERLOCS_PRESERVED


void swapfun(int *arr, int i, int j) {
    int tmp;
    if (arr[i] > arr[j]) {
        tmp = arr[i];
        arr[i] = arr[j];
        arr[j] = tmp;
    }
}




#define LEN_ARR 2

int main(int argc, char **argv)
{
    int arr[LEN_ARR], arr_old[LEN_ARR];
    int i, j, k;
    for (k = 0; k < LEN_ARR; k++) {
        arr_old[k] = arr[k] = getchar();
    }
    i = 0;
    j = LEN_ARR/2;

#ifdef USE_SWAPFUN
    swapfun(arr, i, j);
#else
    int tmp; 
    if (arr[i] > arr[j]) { 
        tmp = arr[i]; 
        arr[i] = arr[j]; 
        arr[j] = tmp; 
    }
#endif

    /* properties */
#ifdef LOCS_ORDERED
    assert(arr[i] <= arr[j]);
#endif
#ifdef LOC_J_MOVED
    assert(arr_old[j] == arr[i] || arr_old[j] == arr[j]);
#endif
#ifdef LOC_I_MOVED
    assert(arr_old[i] == arr[j] || arr_old[i] == arr[i]);
#endif
#ifdef OTHERLOCS_PRESERVED
    for (k = 0; k < LEN_ARR; k++) {
        if (k != i && k != j) {
            assert(arr_old[k] == arr[k]);
        }
    }
#endif
    return 0;
}
