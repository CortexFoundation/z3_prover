#include "cvm/op.h"
#include "cvm/z3_types.h"

#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

BIN_OP_FUNC(op_add, a, b) {
  return a + b;
};
BIN_PREC_FUNC(prec_add, a, b) {
  return type::op_max(a, b) + 1;
};

Z3_REGISTER_OP(broadcast_add)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_generator(prove_gen(op_add, prec_add));
  // .set_generator(binary_op_prove<op_add, prec_add>);

BIN_OP_FUNC(op_sub, a, b) {
  return a - b;
};
BIN_PREC_FUNC(prec_sub, a, b) {
  return type::op_max(a, b) + 1;
};

Z3_REGISTER_OP(broadcast_sub)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_generator(prove_gen(op_sub, prec_sub));

BIN_OP_FUNC(op_mul, a, b) {
  return a * b;
};
BIN_PREC_FUNC(prec_mul, a, b) {
  return a + b;
};

/*
 * The model is deterministic.
 * Time: 3574.77s
 **/
Z3_REGISTER_OP(broadcast_mul)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_generator(prove_gen(op_mul, prec_mul));

BIN_OP_FUNC(op_div, a, b) {
  return a / b;
};
BIN_PREC_FUNC(prec_div, a, b) {
  return a;
};

Z3_REGISTER_OP(broadcast_div)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_generator(prove_gen(op_div, prec_div));

BIN_OP_FUNC(op_max, a, b) {
  return type::op_max(a, b);
};
BIN_PREC_FUNC(prec_max, a, b) {
  return type::op_max(a, b);
};

Z3_REGISTER_OP(broadcast_max)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_generator(prove_gen(op_max, prec_max));

}
}
