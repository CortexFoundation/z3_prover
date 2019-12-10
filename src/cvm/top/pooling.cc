#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

BIN_OP_FUNC(op_max, a, b) {
  return type::op_max(a, b);
};
BIN_PREC_FUNC(prec_max, a, b) {
  return type::op_max(a, b);
};

Z3_REGISTER_OP(max_pool2d)
  .set_generator(prove_gen(op_max, prec_max));

}
}
