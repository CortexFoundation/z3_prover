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

std::vector<z3_expr> _flatten_prove() {
  /**
   * Flatten operator does nothing except memory copy,
   *  which is equals with assign process defined in
   *  `z3_types.cc` that is deterministic.
   *
   * Refers to cvm-runtime:src/cvm/ops/cpu/elemwise.cc
   *  Line:83 for more details.
   **/
  return {};
}

Z3_REGISTER_OP(flatten)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_generator(_flatten_prove);

std::vector<z3_expr> _reshape_prove() {
  /**
   * Reshape operator does nothing except memory copy,
   *  which is equals with assign process defined in
   *  `z3_types.cc` that is deterministic.
   *
   * Refers to cvm-runtime:src/cvm/ops/cpu/elemwise.cc
   *  Line:104 for more details.
   **/
  return {};
}

Z3_REGISTER_OP(reshape)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_generator(_reshape_prove);

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

Z3_REGISTER_OP(cvm_clip)
  .set_num_inputs(1)
  .set_num_outputs(1)
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

Z3_REGISTER_OP(cvm_right_shift)
  .set_num_inputs(1)
  .set_num_outputs(1)
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

Z3_REGISTER_OP(cvm_left_shift)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_generator(_cvm_left_shift_prove);

}
}
