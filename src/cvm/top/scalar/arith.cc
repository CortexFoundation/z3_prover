#include "cvm/op.h"

namespace z3 {
namespace cvm {

std::vector<Op> _scalar_add(const NodeAttrs& attrs,
                std::vector<Op>& inputs) {
  
}
      

Z3_REGISTER_OP(scalar_add)
.set_num_inputs(2)
.set_num_outputs(1)
.set_forward(_scalar_add);

}
}
