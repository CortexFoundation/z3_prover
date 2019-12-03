#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

#define HOLDER const auto &

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

  const auto &v = op(a->at(0), b->at(0));
  const auto &p = ip(a->prec, b->prec);
  TypePtr res = Scalar::Make(v, p)->copy("out");

  z3_expr cstr = 
    TypeRef::collect_constraints({a, b}) &&
    res->assign_constraints() &&
    res->prec_constrains();
  z3_expr asrt = 
    res->data_constraints() && 
    res->op_constraints();
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
 **/
infer_precision _add_prec = [](const z3_expr &a, const z3_expr &b) {
  return type::op_max(a, b) + 1;
};

val_forward _add_f = 
  [](const std::vector<TypePtr> &ins) -> std::vector<z3_expr> {
  return { ins[0]->at(0) + ins[1]->at(0) };
};
prec_forward _add_pf = 
  [](const std::vector<TypePtr> &ins) -> std::vector<z3_expr> {
    const auto &a = ins[0]->prec;
    const auto &b = ins[1]->prec;
    return { type::op_max(a, b) + 1 };
  };

Z3_REGISTER_OP(elemwise_add)
  .set_num_inputs(2)
  .set_num_outputs(1)
  // .set_forward(elemwise_op<_add, _add_prec>)
  .set_generator(OP_PROVE<_add_f, _add_pf, NULL_EC, 2, 1>);
  // .set_generator(elemwise_op_prove<_add, _add_prec>);

op_forward _sub = [](const z3_expr &a, const z3_expr &b) {
  return a - b;
};
infer_precision _sub_prec = [](const z3_expr &a, const z3_expr &b) {
  return type::op_max(a, b) + 1;
};

Z3_REGISTER_OP(elemwise_sub)
  .set_num_inputs(2)
  .set_num_outputs(1)
  // .set_forward(elemwise_op<_sub, _sub_prec>)
  .set_generator(elemwise_op_prove<_sub, _sub_prec>);

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
    res->prec_constrains();
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
    res->prec_constrains();
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
    res->prec_constrains();
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
    res->prec_constrains();
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
