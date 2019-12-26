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

static void RepeatAttrDefault(NodeAttrs& attrs) {
  ATTR_DECL(attrs, "repeats");
  ATTR_DEFAULT(attrs, "axis", "0");
}

static void RepeatForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  
  TypePtr const& x = inputs.at(0);
  TypePtr& y = outputs.at(0);
  std::string const s_repeats = attrs.dict.at("repeats");
  int repeats = std::atoi(s_repeats.c_str());
  std::string s_axis = attrs.dict.at("axis");
  int axis = std::atoi(s_axis.c_str());
  int ndims = inputs[0]->ndim();
  if (axis < 0) {
    axis += ndims;
  }
  for (size_t i = 0; i < y->Size(); ++i) {
    size_t o_i = i, in_i = 0, shapeSize = 1;
    for (int j = ndims-1; j >= 0; j--) {
      size_t col = o_i % y->shape[j];
      o_i /= y->shape[j];
      if (j == axis) {
        col = col / repeats;
      }
      in_i += col *shapeSize;
      shapeSize *= x->shape[j];
    }
    y->set_data(i, x->at(in_i));
    nas[0].at(i)
      .add_input(x, in_i)
      .add_output(y, i);
  }
}

static void RepeatInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 1U);
  std::string const s_repeats = attrs.dict.at("repeats");
  int repeats = std::atoi(s_repeats.c_str());
  VERIFY_EQ(repeats > 0, true);
  std::string s_axis = attrs.dict.at("axis");
  int axis = std::atoi(s_axis.c_str());
  int ndims = ishpes.at(0).size();
  VERIFY_EQ((-ndims <= axis) && (axis < ndims), true); 
  const int pivot = axis < 0 ? ndims + axis : axis;
  for (int i = 0; i < pivot; ++i) {
    oshpes[0].emplace_back(ishpes[0].at(i));
  }

  oshpes[0].emplace_back(ishpes[0].at(pivot) * repeats);
  for (int i = pivot+1; i < ndims; ++i) {
    oshpes[0].emplace_back(ishpes[0].at(i));
  }
}

static void RepeatInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {

  oprecs[0] = iprecs.at(0);

}

Z3_REGISTER_OP(repeat)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(RepeatAttrDefault)
  .set_forward(RepeatForward)
  .set_infer_shape(RepeatInferShape)
  .set_infer_precision(RepeatInferPrecision)
  ;

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

static void FlattenForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  TypePtr& x = inputs.at(0);
  TypePtr& y = outputs.at(0);

  for (size_t i = 0; i < x->Size(); ++i) {
    y->set_data(i, x->at(i));
    nas[0][i].add_input(x, i)
        .add_output(y, i);
  }
}

static void FlattenInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), static_cast<size_t>(1));
  VERIFY_EQ(oshpes.size(), static_cast<size_t>(1));
  const auto& dshape = ishpes[0]; 
  uint32_t target_dim = 1;
  for (int i = 1; i < dshape.size(); i++) {
    target_dim *= dshape[i];
  }
  oshpes[0] = Shape();
  oshpes[0].push_back(dshape[0]);
  oshpes[0].push_back(target_dim);
}


static void FlattenInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  
    oprecs[0] = iprecs.at(0);
}

Z3_REGISTER_OP(flatten)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_forward(FlattenForward)
  .set_infer_shape(FlattenInferShape)
  .set_infer_precision(FlattenInferPrecision)
  .set_generator(_flatten_prove);

static void TileForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  TypePtr& x = inputs.at(0);
  TypePtr& y = outputs.at(0);

  int32_t yndim = y->ndim();
  int32_t xndim = x->ndim();
  
  uint64_t tmp_y_size = 1;

  for (int i = 0; i < xndim; i++) {
    tmp_y_size *= y->shape[i+yndim-xndim];
  }

  for (uint64_t i = 0; i < tmp_y_size; i++) {
    uint64_t o_i = i, in_i = 0, shapeSize = 1;
    for (int j = xndim-1; j >= 0; j--) {
      int yj = j + yndim - xndim;
      int col = o_i % y->shape[yj];
      o_i /= y->shape[yj];
      col = col %  x->shape[j];
      in_i += col * shapeSize;
      shapeSize *= x->shape[j];
    }
    y->set_data(i, x->at(in_i));
    nas[0][i].add_input(x, in_i)
      .add_output(y, i);
  }

  uint64_t othery = 1;
  for (size_t i = 0; i < yndim-xndim; ++i) {
    othery *= y->shape[i];
  }
  for (size_t i = 1; i < othery; i++) {
    for (size_t j = 0; j < tmp_y_size; j++) {
      y->set_data(i*tmp_y_size + j, y->at(j));
      nas[0].at(i*tmp_y_size+j)
        .add_input(y, j)
        .add_output(y, i*tmp_y_size + j)
        .set_uid(1);
    }
  }
}

static void TileInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), static_cast<size_t>(1));
  VERIFY_EQ(oshpes.size(), static_cast<size_t>(1));
  const Shape& shp = ishpes[0]; 
  uint32_t sdim = shp.size();
 
  Shape reps = Shape::from_string(attrs.dict.at("reps"));
  uint32_t rdim = reps.size();
  VERIFY(rdim > 0);
  uint32_t odim = std::max(sdim, rdim);

  for (size_t i = 0; i < rdim; i++) {
    VERIFY((reps[i] >= 1) && (reps[i] < 4096));
  }

  oshpes[0] = Shape();
  for (size_t i = 0; i < odim; i++) {
    oshpes[0].emplace_back(0);
  }
  for (size_t i = 0; i < odim; i++) {
    const auto s = i < sdim ? shp[sdim-1-i] : 1;
    const auto r = i < rdim ? reps[rdim-1-i] : 1;
    oshpes[0][odim-1-i] = s * r;
  }
}


static void TileInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  
    oprecs[0] = iprecs.at(0);
}

static void TileAttrDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "reps", "(0)");
}

Z3_REGISTER_OP(tile)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(TileAttrDefault)
  .set_forward(TileForward)
  .set_infer_shape(TileInferShape)
  .set_infer_precision(TileInferPrecision)
  ;

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
