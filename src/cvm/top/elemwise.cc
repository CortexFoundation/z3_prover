#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

#define HOLDER const auto &

BIN_OP_FUNC(op_add, a, b) {
  return a + b;
};
BIN_PREC_FUNC(prec_add, a, b) {
  return type::op_max(a, b) + 1;
};

static void ElemwiseAddForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  TypePtr const& a = inputs.at(0);
  TypePtr const& b = inputs.at(1);

  for (size_t i = 0; i < a->Size(); ++i) {
    z3_expr const& v = a->at(i) + b->at(i);
    outputs[0]->set_data(i, v);
    nas[0].at(i)
      .add_input(a, i)
      .add_input(b, i)
      .add_output(outputs[0], i);
  }
}

static void ElemwiseAddInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.at(0), ishpes.at(1));
  oshpes.at(0) = ishpes.at(0);
}

static void ElemwiseAddInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  z3_expr max_prec = type::op_max(iprecs.at(0), iprecs.at(1));
  oprecs.at(0) = max_prec + 1;
}
  
Z3_REGISTER_OP(elemwise_add)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_infer_shape(ElemwiseAddInferShape)
  .set_infer_precision(ElemwiseAddInferPrecision)
  .set_forward(ElemwiseAddForward)
  .set_generator(prove_gen(op_add, prec_add));

BIN_OP_FUNC(op_sub, a, b) {
  return a - b;
};
BIN_PREC_FUNC(prec_sub, a, b) {
  return type::op_max(a, b) + 1;
};

static void ElemwiseSubForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  TypePtr const& a = inputs.at(0);
  TypePtr const& b = inputs.at(1);

  for (size_t i = 0; i < a->Size(); ++i) {
    z3_expr const& v = a->at(i) - b->at(i);
    outputs[0]->set_data(i, v);
    nas[0].at(i)
      .add_input(a, i)
      .add_input(b, i)
      .add_output(outputs[0], i);
  }
}

static void ElemwiseSubInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.at(0), ishpes.at(1));
  oshpes[0] = ishpes.at(0);
}

static void ElemwiseSubInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  z3_expr max_prec = type::op_max(iprecs.at(0), iprecs.at(1));
  oprecs[0] = max_prec + 1;
}
  
Z3_REGISTER_OP(elemwise_sub)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_infer_shape(ElemwiseSubInferShape)
  .set_infer_precision(ElemwiseSubInferPrecision)
  .set_forward(ElemwiseSubForward)
  .set_generator(prove_gen(op_sub, prec_sub));

static void ClipAttrDefault(NodeAttrs& attrs) {
  ATTR_DECL(attrs, "a_min");
  ATTR_DECL(attrs, "a_max");
}

static void ClipForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  
  TypePtr const& x = inputs.at(0);
  std::string const s_min = attrs.dict.at("a_min");
  std::string const s_max = attrs.dict.at("a_max");
  int a_min = std::atoi(s_min.c_str());
  int a_max = std::atoi(s_max.c_str());

  for (size_t i = 0; i < x->Size(); ++i) {
    z3_expr const& v = type::op_max(a_min, type::op_min(x->at(i), a_max));
    outputs[0]->set_data(i, v);
    nas[0].at(i)
      .add_input(x, i)
      .add_output(outputs[0], i);
  }
}

static void ClipInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  oshpes[0] = ishpes[0];
}

static void ClipInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  int64_t r = 1;
  r = (r << 31) - r;
  
  std::string const s_min = attrs.dict.at("a_min");
  std::string const s_max = attrs.dict.at("a_max");
  int64_t a_min = std::atoi(s_min.c_str());
  int64_t a_max = std::atoi(s_max.c_str());
  
  VERIFY((a_max >= -r) && (a_max <= r+1));
  VERIFY((a_min >= -r) && (a_min <= r+1));
  VERIFY(a_min < a_max);

  int64_t range = std::max(std::abs(a_min), std::abs(a_max));
  oprecs[0] = GetBit(range) + 1; 
}

std::vector<z3_expr> _clip_prove() {
  TypePtr a = Scalar::Make("a");
  z3_expr a_min("a_min"), a_max("a_max");

  HOLDER v = op_max(op_min(a->at(0), a_max), a_min);
  HOLDER r = op_max(op_abs(a_min), op_abs(a_max));
  HOLDER p = r.get_bit() + 1;
  TypePtr res = Scalar::Make(v, p)->copy("out");

  z3_expr cstr = 
    TypeRef::collect_constraints({a}) &&
    a_min.closed_interval(-Z3_INT32_MAX, Z3_INT32_MAX) &&
    a_max.closed_interval(-Z3_INT32_MAX, Z3_INT32_MAX) &&
    (a_min < a_max) &&
    res->assign_constraints() &&
    res->prec_constraints();
  z3_expr asrt = 
    res->data_constraints() && 
    res->op_constraints();
  return {
    type::implies(cstr, asrt)
  };
}

Z3_REGISTER_OP(clip)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(ClipAttrDefault)
  .set_infer_shape(ClipInferShape)
  .set_infer_precision(ClipInferPrecision)
  .set_forward(ClipForward)
  .set_generator(_clip_prove);

std::vector<z3_expr> _cvm_clip_prove() {
  TypePtr a = Scalar::Make("a");
  z3_expr prec("precision");

  HOLDER max = prec.bit_range();
  HOLDER min = -max;
  HOLDER v = op_max(op_min(a->at(0), max), min);
  HOLDER p = prec;
  TypePtr res = Scalar::Make(v, p)->copy("out");

  z3_expr cstr = 
    TypeRef::collect_constraints({a}) &&
    // Refer to cvm-runtime:src/cvm/top/tensor/elemwise.cc
    //  Line:133 for more details.
    prec.closed_interval(1, 32) &&
    res->assign_constraints() &&
    res->prec_constraints();
  z3_expr asrt = 
    res->data_constraints() && 
    res->op_constraints();
  return {
    type::implies(cstr, asrt)
  };
}

static void CVMClipAttrDefault(NodeAttrs& attrs) {
  ATTR_DECL(attrs, "precision");
  ATTR_DEFAULT(attrs, "is_sign", "true");
}

static void CVMClipInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 1U);
  oshpes.at(0) = ishpes.at(0);
}

static void CVMClipInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  
  std::string const s_min = attrs.dict.at("precision");
  int a_min = std::atoi(s_min.c_str());
  
  VERIFY((a_min >= 1) && (a_min < 33));
  oprecs[0] = a_min;
}

static void CVMClipForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  
  TypePtr const& x = inputs.at(0);
  std::string const str_precision= attrs.dict.at("precision");
  int precision = std::stoi(str_precision);
  int32_t a_min = -(((int64_t)1 << (precision-1))-1);
  int32_t a_max = -a_min;
  
  for (size_t i = 0; i < x->Size(); ++i) {
    z3_expr tmp = x->at(i);
    tmp = op_ite(tmp > a_max,
      a_max, op_ite(tmp < a_min, a_min, tmp));
      
    outputs[0]->set_data(i, tmp);
    nas[0].at(i)
      .add_input(x, i)
      .add_output(outputs[0], i);
  }
}

Z3_REGISTER_OP(cvm_clip)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(CVMClipAttrDefault)
  .set_forward(CVMClipForward)
  .set_infer_shape(CVMClipInferShape)
  .set_infer_precision(CVMClipInferPrecision)
  .set_generator(_cvm_clip_prove);

std::vector<z3_expr> _cvm_right_shift_prove() {
  TypePtr a = Scalar::Make("a");
  z3_expr prec("precision"), shift_bit("shift_bit");

  HOLDER max = prec.bit_range();
  HOLDER min = -max;
  HOLDER shift = op_ite(shift_bit == 1,
      (a->at(0) + 1) >> 1,
      ((a->at(0) >> (shift_bit - 1)) + 1) >> 1);
  HOLDER v = op_max(op_min(shift, max), min);
  HOLDER p = prec;
  TypePtr res = Scalar::Make(v, p)->copy("out");

  z3_expr cstr = 
    TypeRef::collect_constraints({a}) &&
    prec.closed_interval(1, 32) &&
    shift_bit.closed_interval(1, 32) &&
    res->assign_constraints() &&
    res->prec_constraints();
  z3_expr asrt =
    res->data_constraints() &&
    res->op_constraints();
  return {
    type::implies(cstr, asrt)
  };
}

static void CVMRightShiftAttrDefault(NodeAttrs& attrs) {
  ATTR_DECL(attrs, "precision");
  ATTR_DECL(attrs, "shift_bit");
  ATTR_DEFAULT(attrs, "is_sign", "true");
}

static void CVMRightShiftInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 1U);
  oshpes.at(0) = ishpes.at(0);
}

static void CVMRightShiftInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  
  std::string const s_min = attrs.dict.at("precision");
  int a_min = std::atoi(s_min.c_str());
  std::string const s_max = attrs.dict.at("shift_bit");
  int a_max = std::atoi(s_min.c_str());
  
  VERIFY((a_min >= 1) && (a_min < 33));
  VERIFY((a_max >= 1) && (a_max < 33));
  oprecs[0] = a_min; 
}

static void CVMRightShiftForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  
  TypePtr const& a = inputs.at(0);
  std::string const str_precision = attrs.dict.at("precision");
  int precision = std::stoi(str_precision);
  std::string const str_shift_bit = attrs.dict.at("shift_bit");
  int b = std::stoi(str_shift_bit);
 
  int32_t a_min = -(((int64_t)1 << (precision-1)) - 1);
  int32_t a_max = -a_min;
  auto size = a->Size();

  if (b == 1) {
    for(uint64_t i = 0; i < size; i++){
      z3_expr shift_a = (a->at(i) + 1) >> 1;
      shift_a = op_ite(shift_a > a_max,
      a_max, op_ite(shift_a < a_min, a_min, shift_a));
      outputs[0]->set_data(i, shift_a);
      nas[0].at(i)
        .add_input(a, i)
        .add_output(outputs[0], i);
    }
  } else {
    b -= 1;
    {
      for(uint64_t i = 0; i < size; i++){
        z3_expr shift_a = ((a->at(i) >> b) + 1) >> 1;
        shift_a = op_ite(shift_a > a_max,
        a_max, op_ite(shift_a < a_min, a_min, shift_a));
        outputs[0]->set_data(i, shift_a);
        nas[0].at(i)
          .add_input(a, i)
          .add_output(outputs[0], i);
      }
    }
  }
}

Z3_REGISTER_OP(cvm_right_shift)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(CVMRightShiftAttrDefault)
  .set_forward(CVMRightShiftForward)
  .set_infer_shape(CVMRightShiftInferShape)
  .set_infer_precision(CVMRightShiftInferPrecision)
  .set_generator(_cvm_right_shift_prove);

std::vector<z3_expr> _cvm_left_shift_prove() {
  TypePtr a = Scalar::Make("a");
  z3_expr prec("precision"), shift_bit("shift_bit");

  HOLDER max = prec.bit_range();
  HOLDER min = -max;
  HOLDER shift = a->at(0) << shift_bit;
  HOLDER v = op_max(op_min(shift, max), min);
  HOLDER p = prec;
  TypePtr res = Scalar::Make(v, p)->copy("out");

  z3_expr cstr = 
    TypeRef::collect_constraints({a}) &&
    prec.closed_interval(1, 32) &&
    shift_bit.closed_interval(1, 32) &&
    (a->prec + shift_bit).closed_interval(1, 32) &&
    res->assign_constraints() &&
    res->prec_constraints();
  z3_expr asrt =
    res->data_constraints() &&
    res->op_constraints();
  return {
    type::implies(cstr, asrt)
  };
}

static void CVMLeftShiftAttrDefault(NodeAttrs& attrs) {
  ATTR_DECL(attrs, "precision");
  ATTR_DECL(attrs, "shift_bit");
  ATTR_DEFAULT(attrs, "is_sign", "true");
}

static void CVMLeftShiftInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 1U);
  oshpes.at(0) = ishpes.at(0);
}

static void CVMLeftShiftInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  
  std::string const s_min = attrs.dict.at("precision");
  int a_min = std::atoi(s_min.c_str());
  std::string const s_max = attrs.dict.at("shift_bit");
  int a_max = std::atoi(s_min.c_str());
  
  VERIFY((a_min >= 1) && (a_min < 33));
  VERIFY((a_max >= 1) && (a_max < 33));
  oprecs[0] = a_min; 
}

static void CVMLeftShiftForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  
  TypePtr const& a = inputs.at(0);
  std::string const str_precision = attrs.dict.at("precision");
  int precision = std::stoi(str_precision);
  std::string const str_shift_bit = attrs.dict.at("shift_bit");
  int b = std::stoi(str_shift_bit);
 
  int32_t a_min = -(((int64_t)1 << (precision-1)) - 1);
  int32_t a_max = -a_min;
  auto size = a->Size();

  for(uint64_t i = 0; i < size; i++){
    z3_expr shift_a = a->at(i) << b;
    outputs[0]->set_data(i, type::op_max(type::op_min(shift_a, a_max), a_min));
    nas[0].at(i)
      .add_input(a, i)
      .add_output(outputs[0], i);
  }
}

Z3_REGISTER_OP(cvm_left_shift)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(CVMLeftShiftAttrDefault)
  .set_forward(CVMLeftShiftForward)
  .set_infer_shape(CVMLeftShiftInferShape)
  .set_infer_precision(CVMLeftShiftInferPrecision)
  .set_generator(_cvm_left_shift_prove);


static void AbsForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  
  TypePtr const& x = inputs.at(0);

  for (size_t i = 0; i < x->Size(); ++i) {
    z3_expr const& v = type::op_abs(x->at(i));
    outputs[0]->set_data(i, v);
    nas[0].at(i)
      .add_input(x, i)
      .add_output(outputs[0], i);
  }
}

static void AbsInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  oshpes[0] = ishpes[0];
}

static void AbsInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  oprecs.at(0)  = iprecs.at(0); 
}

Z3_REGISTER_OP(abs)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_forward(AbsForward)
  .set_infer_shape(AbsInferShape)
  .set_infer_precision(AbsInferPrecision);

static void NegativeForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  
  TypePtr const& x = inputs.at(0);

  for (size_t i = 0; i < x->Size(); ++i) {
    z3_expr const& v = -x->at(i);
    outputs[0]->set_data(i, v);
    nas[0].at(i)
      .add_input(x, i)
      .add_output(outputs[0], i);
  }
}

static void NegativeInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 1U);
  oshpes.at(0) = ishpes.at(0);
}

static void NegativeInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  oprecs.at(0)  = iprecs.at(0); 
}

Z3_REGISTER_OP(negative)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_forward(NegativeForward)
  .set_infer_shape(NegativeInferShape)
  .set_infer_precision(NegativeInferPrecision);

static void CVMPrecisionForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  
  TypePtr const& x = inputs.at(0);
  TypePtr& y = outputs.at(0);

    for(size_t j = 0; j < x->Size(); j++){
      z3_expr x_val = x->at(j);
      z3_expr v = 32;
      for(int i = 1; i < 32; i++){
        z3_expr tmp = 1 << i;
        z3_expr tmpv = int32_t(1) << v;
        v = op_ite(type::op_abs(x_val) < tmp, op_ite(tmp < tmpv, i, v), v);
      }
       outputs[0]->set_data(j, v);
       nas[0].at(j)
         .add_input(x, j)
         .add_output(outputs[0], j);
    }
}

static void CVMPrecisionInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  oshpes[0] = ishpes[0];
}

static void CVMPrecisionInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  for (auto& v : oprecs){
    v = 6;
  }
}

Z3_REGISTER_OP(cvm_precision)
  .set_num_inputs(1)
  .set_num_outputs(1)
  //.set_forward(CVMPrecisionForward)
  .set_infer_shape(CVMPrecisionInferShape)
  .set_infer_precision(CVMPrecisionInferPrecision);
}
}
