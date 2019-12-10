#include "cvm/z3_types.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

std::vector<z3_expr> _sum_prove() {
  return {};
}

Z3_REGISTER_OP(sum)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_generator(_sum_prove);

}
}
