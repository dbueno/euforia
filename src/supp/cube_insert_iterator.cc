#include "supp/cube_insert_iterator.h"

#include "xsys/transition_system.h"

namespace euforia {
namespace detail {
void CubeProxy::operator=(z3::expr e) {
  xc_.cube.push(e, xc_.xsys.prime(e));
}
}
} // end namespace euforia
