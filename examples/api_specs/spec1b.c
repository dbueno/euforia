#include <stdio.h>
#include <stdlib.h>

// y must be obtain from FirstAPI(x)


extern int FirstAPI(int);
extern int SecondAPI(int);
extern void Use(int, int);

int main(int argc, char **argv) {
    int x = getchar(), y = 0;

    if (getchar()) // for example, if option exists in file
        y = FirstAPI(x);
    //SecondAPI(y);

    if (getchar()) 
        Use(x, y);

    return 0;
}
