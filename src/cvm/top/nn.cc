#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

uint32_t UseBiasNumInputs(const NodeAttrs& attrs) {
  return attrs.dict.at("use_bias") == "true" ? 3 : 2;
}

void DenseParamDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "use_bias", "true");
  ATTR_DECL(attrs, "units");
  VERIFY(std::atoi(attrs.dict["units"].c_str()) >= 1)
    << "operator " << attrs.op->name
    << "(" << attrs.name << ")"
    << " unit attribute must larger than 1";
}

void DenseForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  Shape xshp = inputs.at(0)->shape;
  Shape wshp = inputs.at(1)->shape;
  Shape oshape = outputs.at(0)->shape;

  // Data forward
  for (int di = 0; di < oshape[0]; ++di) {
    int y_offset = di * oshape[1];
    int x_offset = di * xshp[1];
    for (int oi = 0; oi < oshape[1]; ++oi) {
      z3_expr sum = 0;
      int w_offset = oi * wshp[1];
      for (int xi = 0; xi < xshp[1]; ++xi) {
        z3_expr tmp = inputs.at(0)->at(x_offset + xi) * 
          inputs.at(1)->at(w_offset + xi);
        nas[0].at(y_offset + oi)
          .add_input(inputs.at(0), x_offset + xi)
          .add_input(inputs.at(1), w_offset + xi);
        sum = sum + tmp;
      }

      if (attrs.dict.at("use_bias") == "true") {
        sum = sum + inputs.at(2)->at(oi);
        nas[0].at(y_offset + oi).add_input(inputs.at(2), oi);
      }
      outputs[0]->set_data(y_offset + oi, sum);
      nas[0].at(y_offset + oi)
        .add_output(outputs[0], y_offset + oi);
    }
  }
}

void DenseInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  Shape xshp = ishpes[0];
  int num_inputs = xshp[xshp.size() - 1];
  z3_expr oprec = iprecs[0] + iprecs[1] + GetBit(num_inputs);
  if (attrs.dict.at("use_bias") == "true") {
    oprec = type::op_max(oprec, iprecs[2]) + 1;
  }
  oprecs[0] = oprec;
  nas[0].add_extra_constraint(iprecs[0] <= 8)
    .add_extra_constraint(iprecs[1] <= 8);
}

void DenseInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  if (attrs.dict.at("use_bias") == "true") {
    VERIFY_EQ(ishpes.size(), 3U) << "Input:[data, weight, bias]";
  } else {
    VERIFY_EQ(ishpes.size(), 2U) << "Input:[data, weight]";
  }
  Shape xshp = ishpes[0], wshp = ishpes[1];
  VERIFY_EQ(xshp.size(), 2U);
  VERIFY_EQ(wshp.size(), 2U);

  int batch = xshp[0], num_inputs = xshp[1];
  int units = std::atoi(attrs.dict.at("units").c_str());
  VERIFY_EQ(wshp, Shape({units, num_inputs}));
  if (attrs.dict.at("use_bias") == "true") {
    VERIFY_EQ(ishpes[2], Shape({units}));
  }

  oshpes[0] = {batch, units};
}

Z3_REGISTER_OP(dense)
  .set_num_inputs(UseBiasNumInputs)
  .set_attr_default(DenseParamDefault)
  .set_infer_shape(DenseInferShape)
  .set_infer_precision(DenseInferPrecision)
  .set_forward(DenseForward)
  .set_num_outputs(1);

void ReluForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr> &inputs,
    std::vector<TypePtr> &outputs,
    std::vector<std::vector<NodeAssertions> > &nas) {
  auto const& x = inputs.at(0);
  auto const& out = outputs.at(0);
  
  for (size_t i = 0; i < out->Size(); ++i) {
    auto const& d = x->at(i);
    auto new_val = type::op_ite(d<0, 0, d);
    out->set_data(i, new_val);
    nas[0].at(i)
      .add_input(x, i)
      .add_output(out, i);
  }
}

Z3_REGISTER_OP(relu)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_infer_shape(SameShape)
  .set_infer_precision(SamePrecision)
  .set_forward(ReluForward);

}
}
