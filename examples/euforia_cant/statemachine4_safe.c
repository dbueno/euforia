#include "svcomp.h"

// This example the property holds.
// But if the preimage thing doesn't substitute the inputs with their values, it says there is a counterexample.

int main(int argc, char **argv)
{
	unsigned u = 0, v = 0;			/// State variables
	unsigned state = 0;				/// State variable

	while (1) {
		__VERIFIER_assert((u + v) < 8);
		state = (state == 0) ? 1 :
				(state == 1) ? 2 :
				(state == 2) ? 3 :
				(state == 3) ? 4 :
				(state == 4) ? 5 : state;
		unsigned a = __VERIFIER_nondet_uint(), b = __VERIFIER_nondet_uint();		/// Inputs
		if ((state == 1) && (a < 3))
			u = a;
		if ((state == 3) && (b < 5))
			v = b;
	}
	return 0;
}
