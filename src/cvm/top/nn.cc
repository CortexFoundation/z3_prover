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
    std::vector<NodeAssertions>& nas) {
  // Infer shape
  if (attrs.dict.at("use_bias") == "true") {
    VERIFY_EQ(inputs.size(), 3U) << "Input:[data, weight, bias]";
  } else {
    VERIFY_EQ(inputs.size(), 2U) << "Input:[data, weight]";
  }
  Shape xshp = inputs.at(0)->shape;
  Shape wshp = inputs.at(1)->shape;
  VERIFY_EQ(inputs.at(0)->ndim(), 2U);
  VERIFY_EQ(inputs.at(1)->ndim(), 2U);
  Shape oshape = xshp;
  int num_inputs = oshape[oshape.size() - 1];
  int units = std::atoi(attrs.dict.at("units").c_str());
  oshape[oshape.size() - 1] = units;
  VERIFY_EQ(wshp, Shape({units, num_inputs}));
  if (attrs.dict.at("use_bias") == "true") {
    VERIFY_EQ(inputs.at(2)->shape, Shape({units}));
  }

  // Infer precision
  TypePtr out = TypeRef::Make(attrs.name, oshape);
  nas.resize(oshape.Size(), NodeAssertions()
        .add_extra_constraint(
          (inputs.at(0)->prec <= 8) &&
          (inputs.at(1)->prec <= 8) ));
  z3_expr oprec = 
    inputs.at(0)->prec + inputs.at(1)->prec +
    GetBit(num_inputs);
  if (attrs.dict.at("use_bias") == "true") {
    oprec = type::op_max(oprec, inputs.at(2)->prec) + 1;
  }
  out->set_prec(oprec);

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
        nas[y_offset + oi]
          .add_input(inputs.at(0), x_offset + xi)
          .add_input(inputs.at(1), w_offset + xi);
        sum = sum + tmp;
      }

      if (attrs.dict.at("use_bias") == "true") {
        sum = sum + inputs.at(2)->at(oi);
        nas[y_offset + oi].add_input(inputs.at(2), oi);
      }
      out->set_data(y_offset + oi, sum);
      nas[y_offset + oi]
        .add_output(out, y_offset + oi);
    }
  }
  outputs.push_back(std::move(out));
}

std::vector<NodeAssertions> 
DenseInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs) {
  Shape xshp = ishpes[0];
  int num_inputs = xshp[xshp.size() - 1];
  z3_expr oprec = iprecs[0] + iprecs[1] + GetBit(num_inputs);
  if (attrs.dict.at("use_bias") == "true") {
    oprec = type::op_max(oprec, iprecs[2]) + 1;
  }
  oprecs[0] = oprec;
  return {
    NodeAssertions()
      .add_extra_constraint(iprecs[0] <= 8)
      .add_extra_constraint(iprecs[1] <= 8)
  };
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
  Shape oshape = xshp;
  int num_inputs = oshape[oshape.size() - 1];
  int units = std::atoi(attrs.dict.at("units").c_str());
  oshape[oshape.size() - 1] = units;
  VERIFY_EQ(wshp, Shape({units, num_inputs}));
  if (attrs.dict.at("use_bias") == "true") {
    VERIFY_EQ(ishpes[2], Shape({units}));
  }
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
    std::vector<NodeAssertions> &nas) {
  auto const& x = inputs.at(0);
  auto const& out = outputs.at(0);
  
  for (size_t i = 0; i < out->Size(); ++i) {
    auto const& d = x->at(i);
    auto new_val = type::op_ite(d<0, 0, d);
    out->set_data(i, new_val);
    nas[i].add_input(x, i)
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
