#ifndef COMMON_H
#define COMMON_H

#include "cvm/z3_types.h"

namespace z3{
namespace cvm {

using val_forward = std::function<
  std::vector<type::z3_expr>(const std::vector<type::TypePtr>&)>;
using prec_forward = std::function<
  std::vector<type::z3_expr>(const std::vector<type::TypePtr>&)>;
using extra_constraints = std::function<
  std::vector<type::z3_expr>(const std::vector<type::TypePtr>&)>;

extra_constraints NULL_EC = 
  [](const std::vector<type::TypePtr>&) -> std::vector<type::z3_expr> {
    return {};
  };

template<
  const val_forward &op, 
  const prec_forward &ip,
  const extra_constraints &ec,
  size_t in_num = 1, size_t out_num = 1>
std::vector<type::z3_expr> OP_PROVE() {
  std::vector<type::TypePtr> trs;
  for (size_t i = 0; i < in_num; ++i) {
    trs.emplace_back(type::Scalar::Make("in_" + std::to_string(i)));
  }

  const auto &v = op(trs);
  const auto &p = ip(trs);
  const auto &c = ec(trs);
  VERIFY_EQ(out_num, v.size())
    << "operator forward function invalid, "
    << "Expected output number " << out_num
    << " vs. " << v.size();
  VERIFY_EQ(out_num, p.size())
    << "precision forward function invalid, "
    << "Expected output number " << out_num
    << " vs. " << p.size();
  VERIFY((c.size() == 0) || (c.size() == v.size()))
    << "extra constraints forward function invalid, "
    << "Expected output number 0|" << out_num
    << " vs. " << c.size();

  std::vector<type::z3_expr> proves;
  for (size_t i = 0; i < out_num; ++i) {
    type::TypePtr out = type::Scalar::Make(
        v[i], p[i])->copy("out_" + std::to_string(i));
    type::z3_expr cstr =
      type::TypeRef::collect_constraints(trs) &&
      ((c.size() == 0) ? true : c[i]) &&
      out->assign_constraints() &&
      out->prec_constrains();
    type::z3_expr asrt =
      out->data_constraints() &&
      out->op_constraints();
    proves.emplace_back(type::implies(cstr, asrt));
  }
  return proves;
}

}
}


#endif // COMMON_H
