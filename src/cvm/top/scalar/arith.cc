#include "cvm/op.h"

namespace z3 {
namespace cvm {

std::vector<TypePtr> _scalar_add(const NodeAttrs& attrs,
                std::vector<TypePtr>& inputs) {
  IntPrim &&a = inputs.at(0)->asscalar();
  IntPrim &&b = inputs.at(1)->asscalar();
  return {
    Scalar::Make(a.val + b.val, 
                 z3::max(a.prec, b.prec) + 1)
  };
}
      

Z3_REGISTER_OP(scalar_add)
.set_num_inputs(2)
.set_num_outputs(1)
.set_forward(_scalar_add);

}
}
