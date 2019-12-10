#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

Z3_REGISTER_OP(repeat)
  .set_generator(null_generator);

Z3_REGISTER_OP(tile)
  .set_generator(null_generator);

Z3_REGISTER_OP(flatten)
  .set_generator(null_generator);

Z3_REGISTER_OP(concatenate)
  .set_num_inputs(kVarg)
  .set_generator(null_generator);

Z3_REGISTER_OP(expand_dims)
  .set_generator(null_generator);

Z3_REGISTER_OP(reshape)
  .set_generator(null_generator);

Z3_REGISTER_OP(squeeze)
  .set_generator(null_generator);

Z3_REGISTER_OP(transpose)
  .set_generator(null_generator);

Z3_REGISTER_OP(slice)
  .set_generator(null_generator);

Z3_REGISTER_OP(take)
  .set_generator(null_generator);

Z3_REGISTER_OP(cvm_lut)
  .set_generator(null_generator);

Z3_REGISTER_OP(slice_like)
  .set_num_inputs(2)
  .set_generator(null_generator);

}
}
