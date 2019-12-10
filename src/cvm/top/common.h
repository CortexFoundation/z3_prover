#ifndef COMMON_H
#define COMMON_H

#include "cvm/z3_types.h"
#include "cvm/op.h"

namespace z3{
namespace cvm {

using _BaseType = std::function<
  std::vector<type::z3_expr>(
      const std::vector<type::z3_expr> &ins,
      const std::vector<type::z3_expr> &attrs)>;
using op_forward = _BaseType;
using prec_forward = _BaseType;
using extra_constraints = std::function<
  std::vector<type::z3_expr>(
      const std::vector<type::z3_expr> &datas,
      const std::vector<type::z3_expr> &precs,
      const std::vector<type::z3_expr> &attrs)>;

template<
  op_forward &&op,
  prec_forward &&ip,
  extra_constraints && ec,
  int in_num = 1, int out_num = 1>
class OpProve {
  std::vector<std::string> attr_names;
 public:
  OpProve(const std::vector<std::string> &attrs)
      : attr_names(attrs) {}

  std::vector<type::z3_expr> operator() () {
    std::vector<type::TypePtr> trs;
    std::vector<type::z3_expr> datas;
    std::vector<type::z3_expr> precs;
    for (int i = 0; i < in_num; ++i) {
      trs.emplace_back(
          type::Scalar::Make("in_" + std::to_string(i)));
      datas.emplace_back(trs[i]->at(0));
      precs.emplace_back(trs[i]->prec);
    }

    std::vector<type::z3_expr> attrs;
    for (const auto &name : attrs) {
      attrs.emplace_back(name);
    }

    const auto &vs = op(datas, attrs);
    const auto &ps = ip(precs, attrs);
    const auto &cs = ec(datas, precs, attrs);
    VERIFY_EQ(vs.size(), out_num)
      << "Invalid op forward size, Expected "
      << out_num << " vs. " << vs.size();
    VERIFY_EQ(ps.size(), out_num)
      << "Invalid prec forward size, Expected "
      << out_num << " vs. " << ps.size();
    VERIFY_EQ(cs.size(), out_num)
      << "Invalid extra constraints size, Expected "
      << out_num << " vs. " << cs.size();

    std::vector<type::z3_expr> proves;
    for (int i = 0; i < out_num; ++i) {
      type::TypePtr res = 
        type::Scalar::Make(vs[i], ps[i]) ->
          copy("out_" + std::to_string(i));
      type::z3_expr cstr =
        type::TypeRef::collect_constraints(trs) &&
        (cs.size() == 0 ? true : cs[i]) &&
        res->assign_constraints() &&
        res->prec_constrains();
      type::z3_expr asrt =
        res->data_constraints() &&
        res->op_constraints();
      proves.emplace_back(type::implies(cstr, asrt));
    }

    return proves;
  }
};

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
      res->prec_constrains();
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

}
}


#endif // COMMON_H
