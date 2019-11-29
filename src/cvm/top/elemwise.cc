#include "cvm/op.h"
#include "cvm/node.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

using op_forward =
  std::function<z3_expr(const z3_expr&, const z3_expr&)>;
using infer_precision =
  std::function<z3_expr(const z3_expr&, const z3_expr&)>;

template<op_forward &op, infer_precision &ip>
z3_expr elemwise_op(
    const NodeAttrs &attrs,
    std::vector<TypePtr> &inputs,
    std::vector<TypePtr> &outputs) {
  const TypePtr &a = inputs.at(0);
  const TypePtr &b = inputs.at(1);

  VERIFY_EQ(a->shape, b->shape)
    << "Inputs shape must be consistent "
    << a->shape.to_string() << " vs. "
    << b->shape.to_string();

  TypePtr res = TypeRef::Make(attrs.name, a->shape);
  for (size_t i = 0; i < a->Size(); ++i) {
    res->at(i) = op(a->at(i), b->at(i));
  }
  res->prec = ip(a->prec, b->prec);
  outputs.emplace_back(res);
  return (a->prec < 32) && (b->prec < 32);
}

template<op_forward &op, infer_precision &ip>
std::vector<z3_expr> elemwise_op_prove() {
  TypePtr a = Scalar::Make("a");
  TypePtr b = Scalar::Make("b");

  z3_expr cstr = a->data_constraints() && b->data_constraints();

  const auto &v = op(a->at(0), b->at(0));
  const auto &p = ip(a->prec, b->prec);
  TypePtr res = Scalar::Make(v, p);

  cstr = cstr && p.closed_interval(1, 32);
  z3_expr asrt = res->data_constraints() && res->op_constraints();
  return {
    type::implies(cstr, asrt)
  };
}

op_forward _add = [](const z3_expr &a, const z3_expr &b) {
  return a + b;
};
/*
 * BinaryPlusPrecision -> 
 *  cvm-runtime:src/cvm/top/tensor/elemwise.cc Line:42
 *
 **/
infer_precision _add_prec = [](const z3_expr &a, const z3_expr &b) {
  return type::op_max(a, b) + 1;
};

Z3_REGISTER_OP(elemwise_add)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_forward(elemwise_op<_add, _add_prec>)
  .set_generator(elemwise_op_prove<_add, _add_prec>);

op_forward _sub = [](const z3_expr &a, const z3_expr &b) {
  return a - b;
};
infer_precision _sub_prec = [](const z3_expr &a, const z3_expr &b) {
  return type::op_max(a, b) + 1;
};

Z3_REGISTER_OP(elemwise_sub)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_forward(elemwise_op<_sub, _sub_prec>)
  .set_generator(elemwise_op_prove<_sub, _sub_prec>);

std::vector<z3_expr> _clip_prove() {
  TypePtr a = Scalar::Make("a");
  z3_expr a_min("a_min"), a_max("a_max");

  z3_expr cstr = a->data_constraints() &&
    a_min.closed_interval(-Z3_INT32_MAX, Z3_INT32_MAX) &&
    a_max.closed_interval(-Z3_INT32_MAX, Z3_INT32_MAX);

  z3_expr v = op_max(op_min(a->at(0), a_max), a_min);
  z3_expr r = op_max(op_abs(a_min), op_abs(a_max));
  z3_expr p = r.get_bit() + 1;
  TypePtr res = Scalar::Make("result");
  cstr = cstr && res->assign(Scalar::Make(v, p));
  // TypePtr res = Scalar::Make(v, p);
  z3_expr asrt = res->data_constraints() && res->op_constraints();
  return {
    type::implies(cstr, asrt)
  };
}

Z3_REGISTER_OP(clip)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_generator(_clip_prove);

}
}
