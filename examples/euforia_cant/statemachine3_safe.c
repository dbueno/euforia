#include "svcomp.h"

// property holds
int main(int argc, char **argv)
{
	unsigned a = __VERIFIER_nondet_int(), b = __VERIFIER_nondet_int();					/// Inputs
	unsigned u = 0, v = 0;			/// State variables
	unsigned state = 0;				/// State variable

        while (1) {
          unsigned state0 = state;
          state = (state == 0) ? 1 :
                          (state == 1) ? 2 :
                          (state == 2) ? 3 :
                          (state == 3) ? 4 :
                          (state == 4) ? 5 : state;
          if (state0 == state)
            break;
          if ((state == 1) && (a < 3))
                  u = a;
          if ((state == 3) && (b < 5))
                  v = b;
          __VERIFIER_assert((u + v) < 8);
        }
	
	return 0;
}

