#include "cvm/op.h"
#include "cvm/node.h"

namespace z3 {
namespace cvm {

z3_expr _add(
    const NodeAttrs &attrs,
    std::vector<TypePtr> &inputs,
    std::vector<TypePtr> &outputs) {
  const TypePtr &a = inputs.at(0);
  const TypePtr &b = inputs.at(1);

  VERIFY_EQ(a->shape, b->shape)
    << "Inputs shape must be consistent "
    << a->shape.to_string() << " vs. "
    << b->shape.to_string();

  TypePtr res = TypeRef::Make(attrs.name, a->shape);
  for (size_t i = 0; i < a->Size(); ++i) {
    res->at(i) = a->at(i) + b->at(i);
  }
  res->prec = type::op_max(a->prec, b->prec) + 1;
  outputs.emplace_back(res);
  return (a->prec < 32) && (b->prec < 32);
}

Z3_REGISTER_OP(elemwise_add)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_forward(_add);

}
}
