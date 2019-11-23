#include "cvm/op.h"
#include "cvm/node.h"

namespace z3 {
namespace cvm {

z3_expr _scalar_add(
    const NodeAttrs &attrs,
    std::vector<TypePtr> &inputs,
    std::vector<TypePtr> &outputs) {
  const TypePtr &a = inputs.at(0);
  const TypePtr &b = inputs.at(1);

  const z3_expr &v = a->asscalar() + b->asscalar();
  const z3_expr &p = z3::type::op_max(a->prec, b->prec) + 1;
  outputs.emplace_back(Scalar::Make(v, p));
  return (a->prec < 32) && (b->prec < 32);
}
      

Z3_REGISTER_OP(scalar_add)
.set_num_inputs(2)
.set_num_outputs(1)
.set_forward(_scalar_add);

}
}
