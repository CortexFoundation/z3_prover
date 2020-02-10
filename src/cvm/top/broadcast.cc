#include "cvm/op.h"
#include "cvm/z3_types.h"

#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

BIN_OP_FUNC(op_add, a, b) {
  return a + b;
};
BIN_PREC_FUNC(prec_add, a, b) {
  return type::op_max(a, b) + 1;
};

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

inline int32_t broadcast_i_index(const Shape& oshape, uint64_t o_index, const Shape& ishape, int idim, int odim){
  if(idim == 1 && ishape[0] == 1) return 0;
  uint64_t index = 0;
  uint64_t allIndex = 1;
  for(int i = 0; i < idim; i++){
    int idx = idim - 1 - i;
    int ovar = o_index % oshape[idx+odim-idim];
    if(ovar < ishape[idx]){
      index += allIndex * ovar;
    }
    allIndex =  allIndex * ishape[idx];
    o_index /= oshape[idx + odim-idim];
  }
  return index;
}

static void BroadcastAddForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  
  TypePtr const& x = inputs.at(0);
  TypePtr const& y = inputs.at(1);
  TypePtr const& z = outputs.at(0);
  for(uint64_t i = 0; i < z->Size(); ++i){
    uint64_t o_index = i;
    int64_t a_index = broadcast_i_index(z->shape, o_index, x->shape, x->ndim(), z->ndim());
    int64_t b_index = broadcast_i_index(z->shape, o_index, y->shape, y->ndim(), z->ndim());
    z3_expr const& v = x->at(a_index) + y->at(b_index);
    outputs[0]->set_data(i, v);
    nas[0].at(i)
      .add_input(x, a_index)
      .add_input(y, b_index)
      .add_output(outputs[0], i);
  }
}

static void BroadcastAddInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 2U);
  VERIFY_EQ(oshpes.size(), 1U);
  const auto& lhs = ishpes.at(0);
  const auto& rhs = ishpes.at(1);

  // avoid pre-mature shape inference.
  VERIFY (lhs.size() != 0 && rhs.size() != 0);

  if (lhs == rhs) {
    oshpes[0] = ishpes[0];
  }
  
  
  Shape out(std::max(lhs.size(), rhs.size()));
  auto bl = out.size() - lhs.size();
  auto br = out.size() - rhs.size();
  for (auto i = 0; i < out.size(); ++i) {
    auto l = 1, r = 1;
    if (i >= bl) l = lhs[i - bl];
    if (i >= br) r = rhs[i - br];
    if (l != r) {
      if (l == 0 || r == 0) {
        out[i] = 0;
      } else {
        VERIFY(l == 1 || r == 1)
          << "operands could not be broadcast together with shapes "
          << ", l=" << l << ", r=" << r;
        out[i] = std::max(l, r);
      }
    } else {
      out[i] = l;
    }
  }
  oshpes[0] = out;
}

static void BroadcastAddInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  VERIFY_EQ(ishpes.size(), 2U);
  auto max_prec = type::op_max(iprecs.at(0), iprecs.at(1));
  oprecs.at(0) = max_prec + 1;
}

Z3_REGISTER_OP(broadcast_add)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_forward(BroadcastAddForward)
  .set_infer_shape(BroadcastAddInferShape)
  .set_infer_precision(BroadcastAddInferPrecision)
  .set_generator(prove_gen(op_add, prec_add));
  // .set_generator(binary_op_prove<op_add, prec_add>);

BIN_OP_FUNC(op_sub, a, b) {
  return a - b;
};
BIN_PREC_FUNC(prec_sub, a, b) {
  return type::op_max(a, b) + 1;
};

static void BroadcastSubForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  
  TypePtr const& x = inputs.at(0);
  TypePtr const& y = inputs.at(1);
  TypePtr const& z = outputs.at(0);
  for(uint64_t i = 0; i < z->Size(); ++i){
    uint64_t o_index = i;
    int64_t a_index = broadcast_i_index(z->shape, o_index, x->shape, x->ndim(), z->ndim());
    int64_t b_index = broadcast_i_index(z->shape, o_index, y->shape, y->ndim(), z->ndim());
    z3_expr const& v = x->at(a_index) - y->at(b_index);
    outputs[0]->set_data(i, v);
    nas[0].at(i)
      .add_input(x, a_index)
      .add_input(y, b_index)
      .add_output(outputs[0], i);
  }
}

static void BroadcastSubInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 2U);
  VERIFY_EQ(oshpes.size(), 1U);
  const auto& lhs = ishpes.at(0);
  const auto& rhs = ishpes.at(1);

  // avoid pre-mature shape inference.
  VERIFY (lhs.size() != 0 && rhs.size() != 0);

  if (lhs == rhs) {
    oshpes[0] = ishpes[0];
  }
  
  
  Shape out(std::max(lhs.size(), rhs.size()));
  auto bl = out.size() - lhs.size();
  auto br = out.size() - rhs.size();
  for (auto i = 0; i < out.size(); ++i) {
    auto l = 1, r = 1;
    if (i >= bl) l = lhs[i - bl];
    if (i >= br) r = rhs[i - br];
    if (l != r) {
      if (l == 0 || r == 0) {
        out[i] = 0;
      } else {
        VERIFY(l == 1 || r == 1)
          << "operands could not be broadcast together with shapes "
          << ", l=" << l << ", r=" << r;
        out[i] = std::max(l, r);
      }
    } else {
      out[i] = l;
    }
  }
  oshpes[0] = out;
}

static void BroadcastSubInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  VERIFY_EQ(ishpes.size(), 2U);
  auto max_prec = type::op_max(iprecs.at(0), iprecs.at(1));
  oprecs.at(0) = max_prec + 1;
}

Z3_REGISTER_OP(broadcast_sub)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_forward(BroadcastSubForward)
  .set_infer_shape(BroadcastSubInferShape)
  .set_infer_precision(BroadcastSubInferPrecision)
  .set_generator(prove_gen(op_sub, prec_sub));

BIN_OP_FUNC(op_mul, a, b) {
  return a * b;
};
BIN_PREC_FUNC(prec_mul, a, b) {
  return a + b;
};

/*
 * The model is deterministic.
 * Time: 3574.77s
 **/
Z3_REGISTER_OP(broadcast_mul)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_generator(prove_gen(op_mul, prec_mul));

BIN_OP_FUNC(op_div, a, b) {
  return a / b;
};
BIN_PREC_FUNC(prec_div, a, b) {
  return a;
};

Z3_REGISTER_OP(broadcast_div)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_generator(prove_gen(op_div, prec_div));

BIN_OP_FUNC(op_max, a, b) {
  return type::op_max(a, b);
};
BIN_PREC_FUNC(prec_max, a, b) {
  return type::op_max(a, b);
};

Z3_REGISTER_OP(broadcast_max)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_generator(prove_gen(op_max, prec_max));

}
}
