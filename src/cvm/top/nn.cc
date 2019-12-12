#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

inline uint32_t UseBiasNumInputs(const NodeAttrs& attrs) {
  return attrs.dict.at("use_bias") == "true" ? 3 : 2;
}

inline void DenseParamDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "use_bias", "true");
  ATTR_DECL(attrs, "units");
  VERIFY(std::atoi(attrs.dict["units"].c_str()) >= 1)
    << "operator " << attrs.op->name
    << "(" << attrs.name << ")"
    << " unit attribute must larger than 1";
}

Z3_REGISTER_OP(dense)
  .set_num_inputs(UseBiasNumInputs)
  .set_attr_default(DenseParamDefault)
  .set_num_outputs(1);

}
}
