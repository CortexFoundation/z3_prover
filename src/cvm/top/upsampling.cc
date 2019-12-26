#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

void UpsamplingParamDefault(NodeAttrs& attrs) {
  ATTR_DECL(attrs, "scale");
  ATTR_DEFAULT(attrs, "layout", "NCHW");
  ATTR_DEFAULT(attrs, "method", "NEAREST_NEIGHBOR")
}

void UpsamplingInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  Shape &dshape = ishpes[0];
  VERIFY_EQ(dshape.size(), 4)
    << "dimension should be 4D, Got: " << dshape.to_string();
  VERIFY_EQ(attrs.dict.at("method"), "NEAREST_NEIGHBOR") 
    << "only accept method = NEAREST_NEIGHBOR ";
  int scale = std::stoi(attrs.dict.at("scale"));
  VERIFY((1 <= scale) && (scale < 4096));
  VERIFY_EQ(attrs.dict.at("layout"), "NCHW");
  Shape oshape = dshape;
  oshape[2] *= scale;
  oshape[3] *= scale;
  oshpes[0] = oshape;
}

void UpsamplingInferPrecision(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<z3_expr> &iprecs,
    std::vector<z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  oprecs[0] = iprecs[0];
}

void UpsamplingForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  int scale = std::stoi(attrs.dict.at("scale"));
  auto x = inputs[0], y = outputs[0];
  for (size_t batch = 0; batch < y->shape[0]; ++batch) {
    for (size_t c = 0; c < y->shape[1]; ++c) {
      for (size_t yi = 0; yi < y->shape[2]; ++yi) {
        for (size_t xi = 0; xi < y->shape[3]; ++xi) {
          size_t y_index = y->shape.FromIndex({batch, c, yi, xi});
          size_t x_index = x->shape.FromIndex(
              {batch, c, yi/scale, xi/scale});
          y->set_data(y_index, x->at(x_index));
          nas[0].at(y_index)
            .add_input(x, x_index)
            .add_output(y, y_index);
        }
      }
    }
  }
}

Z3_REGISTER_OP(upsampling)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(UpsamplingParamDefault)
  .set_infer_shape(UpsamplingInferShape)
  .set_infer_precision(UpsamplingInferPrecision)
  .set_forward(UpsamplingForward)
  .set_generator(null_generator);

}
}
