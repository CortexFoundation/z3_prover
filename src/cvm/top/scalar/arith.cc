#include "cvm/op.h"
#include "cvm/node.h"

namespace z3 {
namespace cvm {

std::vector<TypePtr> _scalar_add(
    const NodeAttrs &attrs,
    std::vector<TypePtr> &inputs) {
  const IntPrim &a = inputs.at(0)->asscalar();
  const IntPrim &b = inputs.at(1)->asscalar();
  return {
    Scalar::Make(a.val + b.val,
                 z3::max(a.prec, b.prec) + 1)
  };
}

expr _constraints(
    const NodeAttrs &attrs,
    std::vector<TypePtr> &inputs) {
  const IntPrim &a = inputs.at(0)->asscalar();
  const IntPrim &b = inputs.at(1)->asscalar();
  return (a.prec < 32) && (b.prec < 32);
}
      

Z3_REGISTER_OP(scalar_add)
.set_num_inputs(2)
.set_num_outputs(1)
.set_constraints(_constraints)
.set_forward(_scalar_add);

}
}
