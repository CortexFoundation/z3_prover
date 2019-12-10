#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

Z3_REGISTER_OP(upsampling)
  .set_generator(null_generator);

}
}
