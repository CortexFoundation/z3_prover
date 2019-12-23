#ifndef COMMON_H
#define COMMON_H

#include "cvm/z3_types.h"
#include "cvm/op.h"
#include "cvm/node.h"

namespace z3{
namespace cvm {

using bin_op_forward = std::function<
  type::z3_expr(const type::z3_expr&, const type::z3_expr&)>;
using bin_prec_forward = std::function<
  type::z3_expr(const type::z3_expr&, const type::z3_expr&)>;

inline func_pg prove_gen(
    bin_op_forward &op,
    bin_prec_forward &ip) {
  return [&]() -> std::vector<type::z3_expr> {
    type::TypePtr a = type::Scalar::Make("a");
    type::TypePtr b = type::Scalar::Make("b");

    const auto &v = op(a->at(0), b->at(0));
    const auto &p = ip(a->prec, b->prec);
    type::TypePtr res = 
      type::Scalar::Make(v, p)->copy("out");

    type::z3_expr cstr = 
      type::TypeRef::collect_constraints({a, b}) &&
      res->assign_constraints() &&
      res->prec_constraints();
    type::z3_expr asrt = 
      res->data_constraints() && 
      res->op_constraints();
    return {
      type::implies(cstr, asrt)
    };
    
  };
}

#define BIN_LAMBDA_DECL_(decl_type, fname, a, b) \
  static bin_ ## decl_type ## _forward fname = \
  [](const type::z3_expr &a, const type::z3_expr &b) -> \
    type::z3_expr

#define BIN_OP_FUNC(name, a, b) \
  BIN_LAMBDA_DECL_(op, name, a, b)
#define BIN_PREC_FUNC(name, a, b) \
  BIN_LAMBDA_DECL_(prec, name, a, b)

inline std::vector<type::z3_expr>
null_generator() {
  return {};
}

inline void SameShape(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U)
    << "SameShape only supported single input";
  for (size_t i = 0; i < oshpes.size(); ++i) {
    oshpes[i] = ishpes[0];
  }
}

inline void SamePrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  VERIFY_EQ(iprecs.size(), 1U)
    << "SameShape only supported single input";
  for (size_t i = 0; i < oprecs.size(); ++i) {
    oprecs[i] = iprecs[0];
  }
}

}
}


#endif // COMMON_H
