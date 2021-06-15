/*
* Rules:
*   1) Don't assert 0
*
* This example fails if numUnits was -1
* NOTE: Modified from original (see pass alternative)
*/

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
#define __VERIFIER_assert(c) if (!(c)) __VERIFIER_error();

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);
extern int __VERIFIER_nondet_int();

extern void NewUnit();
extern void gotUnit();

void getUnit() 
{
    int numUnits = __VERIFIER_nondet_int();
    int level = __VERIFIER_nondet_int();

    int canEnter = 0;
    if (numUnits > 0)
    {
       canEnter = 1;
    }
    else
    {
        if (level > 10)
        {
            NewUnit();
            numUnits = numUnits + 1;
            canEnter = 1;
        }
    }

    if (canEnter)
    {
        if (numUnits == 0)
        {
            __VERIFIER_error();
        }
        else
        {
            gotUnit();
        }
    }
}

int main() { getUnit(); }
