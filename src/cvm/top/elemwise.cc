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

/*static void RepeatAttrDefault(NodeAttrs& attrs) {
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
  ATTR_DEFAULT(attrs, "reps", "()");
}


Z3_REGISTER_OP(tile)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(TileAttrDefault)
  .set_forward(TileForward)
  .set_infer_shape(TileInferShape)
  .set_infer_precision(TileInferPrecision)
  ;

static void ConcatenateAttrDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "axis", "1");
}

inline bool shape_assign(Shape *y, const Shape& x) {
  if (y->size() == 0) {
    *y = x;
    return true;
  } else if (y->size() != x.size()) {
    return x.size() == 0;
  } else {
    for (size_t i = 0; i < y->size(); ++i) {
      if ((*y)[i] == 0) {
        (*y)[i] = x[i];
      } else if ((*y)[i] != x[i] && x[i] != 0) {
        return false;
      }
    }
    return true;
  }
}

static void ConcatenateForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
 
  std::string st_axis = attrs.dict.at("axis");
  int axis = std::stoi(st_axis);
  int ndim = inputs.at(0)->ndim();
  if (axis < 0){
    axis += ndim;
  }

  auto& out_data = outputs.at(0);
  for (uint64_t i = 0; i < out_data->Size(); i++){
    uint64_t o_i = i, in_i = 0, in_i2 = 0, shapeSize = 1;
    for (int j = out_data->ndim()-1; j >= 0; j--){
      uint64_t col = o_i % out_data->shape[j];
      o_i /= out_data->shape[j];
      uint64_t tmpcol = col;
      if (j == axis){
        uint64_t allShapeSize = 0;
        for (int k = 0; k < inputs.size(); k++){
          tmpcol = col - allShapeSize;
          allShapeSize = inputs.at(k)->shape[axis];
          if (col < allShapeSize){
            in_i = k;
            break;
          }
        }
      }
      in_i2 += tmpcol * shapeSize;
      shapeSize *= inputs.at(in_i)->shape[j];
    }
    out_data->set_data(i, inputs.at(in_i)->at(in_i2));
    nas[0][i].add_input(inputs.at(in_i), in_i2)
      .add_output(out_data, i);
  }

}

static void ConcatenateInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY(ishpes.size());
  int ndim = ishpes.at(0).size();
  for (const auto& it : ishpes){
    VERIFY_EQ(it.size(), ndim);
  }

  std::string st_attrs_axis = attrs.dict.at("axis");
  int attrs_axis = std::stoi(st_attrs_axis);
  VERIFY(attrs_axis >= -ndim && attrs_axis < ndim);
  int axis = attrs_axis >= 0 ? attrs_axis : ndim + attrs_axis;

  bool has_zero = false;
  int size = 0;
  Shape dshape;
  for (auto& tmp : ishpes){
    VERIFY(axis < ndim);
    has_zero = tmp[axis] == 0 || has_zero;
    size += tmp[axis];
    tmp[axis] = 0;
    VERIFY_EQ(shape_assign(&dshape, tmp), true);
  }

  Shape tmp = oshpes.at(0);
  if (tmp.size()){
    VERIFY(axis < tmp.size());
    tmp[axis] = 0;
    VERIFY_EQ(shape_assign(&dshape, tmp), true);
  }
  if (!has_zero){
    dshape[axis] = size;
  }
  VERIFY(dshape.Size());
  oshpes.at(0) = dshape;
}

static void ConcatenateInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
    VERIFY(iprecs.size() > 0);
    type::z3_expr max_prec = iprecs.at(0);
    for (auto prec : iprecs) {
      max_prec = type::op_max(prec, max_prec);
    }
    for (auto& v : oprecs){
      v = max_prec;
    }
}

Z3_REGISTER_OP(concatenate)
  .set_num_inputs(kVarg)
  .set_num_outputs(1)
  .set_attr_default(ConcatenateAttrDefault)
  .set_forward(ConcatenateForward)
  .set_infer_shape(ConcatenateInferShape)
  .set_infer_precision(ConcatenateInferPrecision)
  ;

static void ExpandDimsAttrDefault(NodeAttrs& attrs) {
  ATTR_DECL(attrs, "axis");
  ATTR_DEFAULT(attrs, "num_newaxis", "1");
}

static void ExpandDimsForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
 
  auto& out_data = outputs.at(0);
  for (uint64_t i = 0; i < out_data->Size(); i++){
    out_data->set_data(i, inputs.at(0)->at(i));
    nas[0][i].add_input(inputs.at(0), i)
      .add_output(out_data, i);
  }

}

static void ExpandDimsInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  const auto& dshape = ishpes.at(0);
  int ndim = dshape.size();
  std::string st_attrs_axis = attrs.dict.at("axis");
  std::string st_attrs_num_axis = attrs.dict.at("num_newaxis");
  int attrs_axis = std::stoi(st_attrs_axis);
  int attrs_num_axis = std::stoi(st_attrs_num_axis);
  VERIFY(attrs_axis >= -ndim-1 && attrs_axis <= ndim);
  const int32_t ATTR_MIN_VALUE = 0; 
  const int32_t ATTR_MAX_VALUE = 4096;
  VERIFY(attrs_axis >= ATTR_MIN_VALUE && attrs_axis < ATTR_MAX_VALUE);
  int axis = attrs_axis < 0 ? ndim + attrs_axis + 1: attrs_axis;

  for (int i = 0; i < axis; i++){
    oshpes.at(0).push_back(dshape.at(i));
  }
  for (int i = 0; i < attrs_num_axis; i++){
    oshpes.at(0).push_back(1);
  }
  for (int i = axis; i < ndim; i++){
    oshpes.at(0).push_back(dshape.at(i));
  }
}

static void ExpandDimsInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {

  oprecs[0] = iprecs.at(0);

}

Z3_REGISTER_OP(expand_dims)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(ExpandDimsAttrDefault)
  .set_forward(ExpandDimsForward)
  .set_infer_shape(ExpandDimsInferShape)
  .set_infer_precision(ExpandDimsInferPrecision)
  ;

static void SqueezeAttrDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "axis", "()");
}

static void SqueezeForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
 
  auto& out_data = outputs.at(0);
  for (uint64_t i = 0; i < out_data->Size(); i++){
    out_data->set_data(i, inputs.at(0)->at(i));
    nas[0][i].add_input(inputs.at(0), i)
      .add_output(out_data, i);
  }

}

static void SqueezeInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {

  oprecs[0] = iprecs.at(0);

}

static void SqueezeInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 1U);
  const auto& shp = ishpes.at(0);
  int ndim = shp.size();
  std::string st_attrs_axis = attrs.dict.at("axis");
  Shape attrs_axis = Shape::from_string(st_attrs_axis);
  if (attrs_axis.size() == 0){
    for (int i = 0; i < ndim; i++){
      if (shp.at(i) != 1){
        oshpes.at(0).emplace_back(shp.at(i));
      }
    }
  } else {
    
    std::unordered_set<int> axis_checker;
    for (size_t i = 0; i < attrs_axis.size(); ++i) {
      VERIFY((attrs_axis.at(i) >= -ndim) && (attrs_axis.at(i) < ndim));
      int real_axis;
      if (attrs_axis.at(i) < 0) {
        real_axis = attrs_axis.at(i)+ ndim;
      } else {
        real_axis = attrs_axis.at(i);
      }
      axis_checker.insert(real_axis);
    }


    for (int i = 0; i < ndim; ++i) {
      if (axis_checker.find(i) == axis_checker.end()) {
        oshpes.at(0).emplace_back(shp[i]);
      } else {
        VERIFY_EQ(shp[i], 1) << "The squeezed axis must have shape 1!"
                            << "Want to squeeze " << i
                            << ", which has shape" << shp[i];
      }
    }
  }

  if (oshpes.at(0).size() == 0) {
    // Handles the case where all axes are squeezed.
    oshpes.at(0).push_back(1);
  }
}

Z3_REGISTER_OP(squeeze)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(SqueezeAttrDefault)
  .set_forward(SqueezeForward)
  .set_infer_shape(SqueezeInferShape)
  .set_infer_precision(SqueezeInferPrecision)
  ;

static void TransposeAttrDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "axes", "()");
}

static void TransposeInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 1U);
  const auto& shp = ishpes.at(0);
  int ndim = shp.size();
  Shape ret(shp);
  
  std::string st_attrs_axis = attrs.dict.at("axes");
  Shape attrs_axis = Shape::from_string(st_attrs_axis);
  std::cout << attrs_axis.size() << " byr " << shp.size() << std:: endl;
  if (attrs_axis.size() == 0){
    for (int i = 0; i < ndim; i++){
      if (shp.at(i) != 1){
        ret[i] = shp[ndim - 1 - i];
      }
    }
  } else {
    VERIFY_EQ(shp.size(), attrs_axis.size());
    Shape axes(attrs_axis);
    for (size_t i = 0; i < ndim; ++i) {
      int64_t new_axis = axes[i];
      VERIFY((new_axis >= -ndim) && (new_axis < ndim));
      int real_axis;
      if (new_axis < 0) {
        new_axis += ndim;
        axes[i] = new_axis;
      }
      for (int j = 0; j < ndim; j++){
        if (i != j){
          VERIFY(new_axis != axes[j]);
        }
      }
      ret[i] = shp[new_axis];
    }
  }
  oshpes.at(0) = ret;
}

static void TransposeForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
 
  std::string st_attrs_axis = attrs.dict.at("axes");
  Shape axes = Shape::from_string(st_attrs_axis);
  for (uint32_t i = 0; i < axes.size(); i++){
    if (axes[i] < 0){
      axes[i] += inputs.at(0)->ndim();
    }
  } 

  int ndim = outputs.at(0)->ndim();

  auto& out_data = outputs.at(0);
  for (uint64_t i = 0; i < out_data->Size(); i++){
    uint64_t o_i = i, in_i = 0;
    for (int j = ndim - 1; j >= 0; j--){
      uint64_t col = o_i % out_data->shape[j];
      o_i /= out_data->shape[j];
      int xj = j;
      if (axes.size() > 0){
        xj = axes[j];
      } else {
        xj = ndim - 1 - j;
      }
      int xi = 1;
      for (int tx = ndim-1; tx > xj; tx--){
        xi *= inputs.at(0)->shape[tx];
      }
      in_i += col * xi;
    }

    out_data->set_data(i, inputs.at(0)->at(in_i));
    nas[0][i].add_input(inputs.at(0), in_i)
      .add_output(out_data, i);
  }
}

static void TransposeInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {

  oprecs[0] = iprecs.at(0);

}

Z3_REGISTER_OP(transpose)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(TransposeAttrDefault)
  .set_forward(TransposeForward)
  .set_infer_shape(TransposeInferShape)
  .set_infer_precision(TransposeInferPrecision)
  ;

static void StridedSliceAttrDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "begin", "(0)");
  ATTR_DEFAULT(attrs, "end", "(1)");
  ATTR_DEFAULT(attrs, "stride", "()");
}

static void StridedSliceInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  const auto& dshape = ishpes.at(0);
  auto oshape = dshape;
  int num_axis = dshape.size();
 
  std::string st_attrs_begin = attrs.dict.at("begin");
  Shape attrs_begin = Shape::from_string(st_attrs_begin);
  std:: vector<int64_t> begin_vec;
  std::copy(attrs_begin.begin(), attrs_begin.end(), std::back_inserter(begin_vec));
  for (int i = begin_vec.size(); i < num_axis; i++){
    begin_vec.push_back(0);
  }

  std::string st_attrs_end = attrs.dict.at("end");
  Shape attrs_end = Shape::from_string(st_attrs_end);
  std:: vector<int64_t> end_vec;
  std::copy(attrs_end.begin(), attrs_end.end(), std::back_inserter(end_vec));
  for (int i = end_vec.size(); i < num_axis; i++){
    end_vec.push_back(dshape[i]);
  }

  std::string st_attrs_stride = attrs.dict.at("stride");
  Shape attrs_stride = Shape::from_string(st_attrs_stride);
  std:: vector<int64_t> stride_vec;
  std::copy(attrs_stride.begin(), attrs_stride.end(), std::back_inserter(stride_vec));
  for (int i = stride_vec.size(); i < num_axis; i++){
    stride_vec.push_back(1);
  }

  for (int i = 0; i < num_axis; i++) {
    VERIFY(stride_vec.at(i) != 0);
    int64_t begin_range = stride_vec.at(i) < 0 ? -1 : 0;
    int64_t end_range = stride_vec.at(i) < 0 ? dshape[i] - 1 : dshape[i];
    int64_t begin = begin_vec.at(i) < 0 ? dshape[i] + begin_vec.at(i) : begin_vec.at(i);
    int64_t end = end_vec.at(i) < 0 ? dshape[i] + end_vec[i] : end_vec[i];
    begin = std::min(std::max(begin, begin_range), end_range);
    end = std::min(std::max(end, begin_range), end_range);
    int interval = std::abs(end - begin);
    int slice_size = static_cast<int>((interval
          + std::abs(stride_vec[i]) - 1) / std::abs(stride_vec[i]));
    VERIFY(stride_vec[i] < 0 ? (end < begin) : (begin < end))
      << ": Input [Begin=" << begin_vec[i] << ", End=" << end_vec[i]
      << "] is invalid for axis=" << i;
    oshape[i] = slice_size;
  }
  oshpes.at(0) = oshape;
}

static void StridedSliceInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {

  oprecs[0] = iprecs.at(0);

}

static void StridedSliceForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
 
  std::string st_begin = attrs.dict.at("begin");
  std::string st_end = attrs.dict.at("end");
  std::string st_stride = attrs.dict.at("stride");
  Shape begin = Shape::from_string(st_begin);
  Shape end = Shape::from_string(st_end);
  Shape stride = Shape::from_string(st_stride);
  auto& x = inputs.at(0);
  auto& y = outputs.at(0);
  int ndim = y->ndim();
  int32_t num_axis = x->ndim();
  Shape dshp = x->shape;
  std::vector<int64_t> begin_vec;
  std::copy(begin.begin(), begin.end(), std::back_inserter(begin_vec));
  for (int i = begin_vec.size(); i < num_axis; ++i) {
    begin_vec.push_back(0);
  }

  std::vector<int64_t> stride_vec;
  std::copy(stride.begin(), stride.end(), 
      std::back_inserter(stride_vec));
  for (int i = stride_vec.size(); i < num_axis; ++i) {
    stride_vec.push_back(1);
  }

  for (size_t i = 0; i < begin_vec.size(); ++i) {
    int64_t begin_range = stride_vec[i] < 0 ? -1 : 0;
    int64_t end_range = stride_vec[i] < 0 ? dshp[i] -1 : dshp[i];
    int64_t begin = begin_vec[i];
    if (begin < 0) begin += dshp[i];
    begin_vec[i]= std::min(std::max(begin, begin_range), end_range);
  }

  
  for(uint64_t i = 0; i < y->Size(); i++){
      uint64_t o_i = i, in_i = 0, shapeSize = 1;
      for(int j = ndim-1; j >= 0; j--){
          uint64_t col = o_i % y->shape[j];
          o_i /= y->shape[j];
          int64_t tbegin = begin_vec[j];
          int64_t tstep = stride_vec[j];
          col = tbegin + col * tstep;
          in_i += col * shapeSize;
          shapeSize *= x->shape[j];
      }
    y->set_data(i, inputs.at(0)->at(in_i));
    nas[0][i].add_input(inputs.at(0), in_i)
      .add_output(y, i);
  }
}

Z3_REGISTER_OP(slice)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(StridedSliceAttrDefault)
  .set_forward(StridedSliceForward)
  .set_infer_shape(StridedSliceInferShape)
  .set_infer_precision(StridedSliceInferPrecision)
  ;

static void SliceLikeAttrDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "axis", "()");
}

static void SliceLikeForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
 
  auto& x = inputs.at(0);
  auto& y = outputs.at(0);
  int ndim = y->ndim();
  
  for(uint64_t i = 0; i < y->Size(); i++){
      uint64_t o_i = i, in_i = 0, shapeSize = 1;
      for(int j = ndim-1; j >= 0; j--){
          int col = o_i % y->shape[j];
          o_i /= y->shape[j];
          in_i += col * shapeSize;
          shapeSize *= x->shape[j];
      }
    y->set_data(i, inputs.at(0)->at(in_i));
    nas[0][i].add_input(inputs.at(0), in_i)
      .add_output(y, i);
  }
}

static void SliceLikeInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 2U);
  VERIFY_EQ(oshpes.size(), 1U);
  const auto& src_shape = ishpes.at(0);
  const Shape& target_shape = ishpes.at(1);
  Shape end_idx = src_shape;

  std::string st_axis = attrs.dict.at("axis");
  Shape axis = Shape::from_string(st_axis);
  if (axis.size() == 0) {
    for (size_t i = 0; i < src_shape.size(); ++i) {
      if (i < target_shape.size()) {
        end_idx[i] = target_shape[i];
        VERIFY(end_idx[i] < src_shape[i])
          << "End index of axis " << i << " exceeds input shape: "
          << end_idx[i] << " vs " << src_shape[i];
      }
    }
  } else {
    for (auto i : axis) {
      VERIFY(((int)-src_shape.size() <= i) && (i < target_shape.size()));
      if (i < 0) {
        i = src_shape.size() + i;
      }
      end_idx[i] = target_shape[i];
      VERIFY(end_idx[i] < src_shape[i])
        << "End index of axis " << i << " exceeds input shape: "
        << end_idx[i] << " vs " << src_shape[i];
    }
  }
  oshpes.at(0) = end_idx;
}

static void SliceLikeInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {

  oprecs[0] = iprecs.at(0);

}

Z3_REGISTER_OP(slice_like)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_attr_default(SliceLikeAttrDefault)
  .set_forward(SliceLikeForward)
  .set_infer_shape(SliceLikeInferShape)
  .set_infer_precision(SliceLikeInferPrecision)
  ;

static void TakeAttrDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "axis", "0");
  ATTR_DEFAULT(attrs, "axis_none", "1");
}

static void TakeInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 2U);
  VERIFY_EQ(oshpes.size(), 1U);
  const auto& dshape = ishpes.at(0);
  const auto& indicesshape = ishpes.at(1);
  int ndim = dshape.size();
  std::string st_axis= attrs.dict.at("axis");
  int in_axis = std::stoi(st_axis);
  std::string st_axis_none = attrs.dict.at("axis_none");
  int in_axis_none = std::stoi(st_axis_none);
  Shape oshape((in_axis_none ? 0 : ndim - 1) + indicesshape.size());


  if (in_axis_none) {
    for (size_t j = 0; j < indicesshape.size(); ++j) {
      oshape[j] = indicesshape[j];
    }
  } else {
    int axis = in_axis;
    VERIFY((axis >= -ndim) && (axis < ndim));
    if (axis < 0) {
      axis += ndim;
    }
    
    size_t posi = 0;
    for (int i = 0; i < ndim; ++i) {
      if (i == axis) {
        for (size_t j = 0; j < indicesshape.size(); ++j) {
          oshape[posi++] = indicesshape[j];
        }
      } else {
        oshape[posi++] = dshape[i];
      }
    }
  }

  ishpes.at(0) = dshape;
  ishpes.at(1) = indicesshape;
  oshpes.at(0) = oshape;
}

static void TakeInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {

  oprecs[0] = iprecs.at(0);

}

static void TakeForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  std::string st_axis= attrs.dict.at("axis");
  int in_axis = std::stoi(st_axis);
  std::string st_axis_none = attrs.dict.at("axis_none");
  int in_axis_none = std::stoi(st_axis_none);
  
  auto& x = inputs.at(0);
  auto& indices = inputs.at(1);
  auto& y = outputs.at(0);
  if (in_axis_none){
    uint64_t xs = x->Size();
    uint64_t ys = y->Size();
    for (uint64_t i = 0; i < ys; i++) {
//      auto in_i = type::op_min(type::op_max(indices->at(i), 0), xs-1);
    }
  } else {
  }

}

Z3_REGISTER_OP(take)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_attr_default(TakeAttrDefault)
  .set_forward(TakeForward)
  .set_infer_shape(TakeInferShape)
  .set_infer_precision(TakeInferPrecision)
  ;

Z3_REGISTER_OP(cvm_lut)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_attr_default(TakeAttrDefault)
  .set_forward(TakeForward)
  .set_infer_shape(TakeInferShape)
  .set_infer_precision(TakeInferPrecision)
  ;

Z3_REGISTER_OP(where)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_attr_default(TakeAttrDefault)
  .set_forward(TakeForward)
  .set_infer_shape(TakeInferShape)
  .set_infer_precision(TakeInferPrecision)
  ;

std::vector<z3_expr> _reshape_prove() {
  return {};
}

static void ReshapeAttrDefault(NodeAttrs& attrs) {
  ATTR_DECL(attrs, "shape");
}

static void ReshapeForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
 
  auto& x = inputs.at(0);
  auto& y = outputs.at(0);
  for(uint64_t i = 0; i < y->Size(); i++){
    y->set_data(i, inputs.at(0)->at(i));
    nas[0][i].add_input(inputs.at(0), i)
      .add_output(y, i);
  }
}

static void ReshapeInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 1U);
  std::string st_shape = attrs.dict.at("shape");
  Shape shape = Shape::from_string(st_shape);
  VERIFY(shape.size() >  0);

  const auto& dshape = ishpes.at(0);
  const Shape& target_shape = shape;
  Shape oshape;
  int src_idx = 0;
  int infer_idx = -1;

  for (int i = 0; i < target_shape.size(); ++i) {
    int64_t svalue = target_shape[i];
    // special flag handling for shape inference.
    if (svalue > 0) {
      oshape.push_back(svalue);
      ++src_idx;
    } else if (svalue == 0) {
      // keep same
      VERIFY(src_idx < dshape.size());
      oshape.push_back(dshape[src_idx++]);
    } else if (svalue == -1) {
      // inference based on rest
      VERIFY(infer_idx < 0)
          << "One and only one dim can be inferred";
      infer_idx = i;
      oshape.push_back(1);
      ++src_idx;
    } else if (svalue == -2) {
      // copy all remaining dims from source
      while (src_idx < dshape.size()) {
        oshape.push_back(dshape[src_idx++]);
      }
    } else if (svalue == -3) {
      // merge two dims from source
      VERIFY(src_idx + 1 < dshape.size());
      int d1 = dshape[src_idx++];
      int d2 = dshape[src_idx++];
      oshape.push_back(d1 * d2);
    } else if (svalue == -4) {
      // split the source dim s into two dims
      // read the left dim and then the right dim (either can be -1)
      VERIFY(i + 2 < target_shape.size());
      VERIFY(src_idx < dshape.size());
      int d0 = dshape[src_idx++];
      int d1 = target_shape[++i];
      int d2 = target_shape[++i];
      VERIFY(d1 != -1 || d2 != -1) << "Split dims cannot both be -1.";
      if (d1 == -1) d1 = d0 / d2;
      if (d2 == -1) d2 = d0 / d1;
      VERIFY_EQ(d1 * d2, static_cast<int>(d0)) <<
          "Split dims " << d1 << ", " << d2 << " do not divide original dim " << d0;
      oshape.push_back(d1);
      oshape.push_back(d2);
    }
  }


  if (infer_idx >= 0) {
    if (dshape.Size() > 0) {
      int new_size = 1;
      for (int x : oshape) {
        new_size *= x;
      }
      oshape[infer_idx] = dshape.Size() / new_size;
    } else {
      oshape[infer_idx] = 0;
    }
  }
  VERIFY_EQ(dshape.Size(), oshape.Size());
  oshpes.at(0) = oshape;
}

static void ReshapeInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {

  oprecs[0] = iprecs.at(0);

}

Z3_REGISTER_OP(reshape)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(ReshapeAttrDefault)
  .set_forward(ReshapeForward)
  .set_infer_shape(ReshapeInferShape)
  .set_infer_precision(ReshapeInferPrecision)
  .set_generator(_reshape_prove);
*/
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
