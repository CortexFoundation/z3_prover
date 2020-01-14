#include "z3++.h"
#include "z3_api.h"

#include "cvm/base.h"
#include "cvm/z3_types.h"
#include "z3_helper.h"

namespace z3 {
namespace type {

context& Z3Context() {
  static context inst;
  return inst;
}

// ===== z3 data & cstr =====

// z3_data::z3_data() : expr(_IntVal(0)) {}
z3_data::z3_data(int num) : expr(_IntVal(num)) {}
z3_data::z3_data(const std::string &name) : expr(_Int(name)) {}
z3_data::z3_data(const char *name) : expr(_Int(name)) {}
z3_data::z3_data(expr val) : expr(val) {
  if (!_IsInt(val)) {
    this->~z3_data(); // Free resource.
    THROW() << "z3_data " << val << " is non data";
  }
}

z3_cstr::z3_cstr() : expr(_BoolVal(true)) {}
z3_cstr::z3_cstr(expr val) : expr(val) { 
  if (!_IsBool(val)) {
    this->~z3_cstr(); // Free resource.
    THROW() << "z3_cstr " << val << " is non constraints";
  }
}

z3_cstr operator&&(const z3_cstr &a, const z3_cstr &b) {
  if (a.is_true()) return b;
  else if (b.is_true()) return a;
#if SIMPLIFY_LEVEL >= 6
  const expr &a_sim = a.simplify();
  const expr &b_sim = b.simplify();
  if (a_sim.is_true()) return b;
  else if (b_sim.is_true()) return a;
  else if (a_sim.is_false() || b_sim.is_false()) 
    return _BoolVal(false);
#endif
  return z3::operator&&(a, b);
}

z3_cstr operator||(const z3_cstr &a, const z3_cstr &b) {
  if (a.is_false()) return b;
  else if (b.is_false()) return a;
#if SIMPLIFY_LEVEL >= 6
  const expr &a_sim = a.simplify();
  const expr &b_sim = b.simplify();
  if (a_sim.is_false()) return b;
  else if (b_sim.is_false()) return a;
  else if (a_sim.is_true() || b_sim.is_true())
    return _BoolVal(true);
#endif
  return z3::operator||(a, b);
}

// ===== z3_expr =====

z3_expr::z3_expr(const std::string &name) : data(name) {}
z3_expr::z3_expr(const char *name) : data(name) {}
z3_expr::z3_expr(int num) : data(num) {}
z3_expr::z3_expr(z3_data data) : data(data) {}

z3_expr::z3_expr(bool flag): data(0), cstr(_BoolVal(flag)) {}
z3_expr::z3_expr(z3_cstr cstr) : data(0), cstr(cstr) {}

z3_expr::z3_expr(z3_data data, z3_cstr cstr) :
  data(data), cstr(cstr) {}

z3_expr z3_expr::deterministic() const {
  return z3_expr(z3_cstr(
        (-Z3_INT32_MAX <= data) && (data <= Z3_INT32_MAX)));
}
z3_expr z3_expr::closed_interval(
    const z3_expr &start, 
    const z3_expr &end) const {
  return z3_expr(z3_cstr(
        (start.data <= data) && (data <= end.data)));
}

z3_expr z3_expr::bit_range() const {
#if SIMPLIFY_LEVEL <= 3
  return func_bit_range(*this);
#else
  return op_one_shl((*this - 1)) - 1;
#endif
}
z3_expr z3_expr::get_bit() const {
  return func_get_bit(*this);
}

#define DATA(name) name.data
#define CSTR(name) name.cstr
#define CSTR_AND(name) c = c && name.cstr

#define FMAP_OP(fname, op, args) \
  F_Z3_EXPR_DECL(fname, args) { \
    z3_data v = _ ## op(EXPAND_ARGS(args, DATA, S_COMMA)); \
    z3_cstr c = _ ## op ## Cstr(EXPAND_ARGS(args, DATA, S_COMMA)); \
    EXPAND_ARGS(args, CSTR_AND, S_SEMI); \
    return z3_expr(v, c); \
  }

FMAP_OP(operator+, Add, 2);
FMAP_OP(operator-, Sub, 2);
FMAP_OP(operator-, Neg, 1);
FMAP_OP(operator*, Mul, 2);
FMAP_OP(operator/, Div, 2);
FMAP_OP(operator<<, Shl, 2);
FMAP_OP(operator>>, Shr, 2);
FMAP_OP(op_one_shl, OneShl, 1);
FMAP_OP(op_max, Max, 2);
FMAP_OP(op_min, Min, 2);
FMAP_OP(op_abs, Abs, 1);
F_Z3_EXPR_DECL(op_ite, 3) {
  z3_data v = _Ite(t1.cstr, t2.data, t3.data);
  z3_cstr c = _IteCstr(t1.cstr, t2.data, t3.data);
  c = c && t2.cstr && t3.cstr;
  return z3_expr(v, c);
}

FMAP_OP(func_bit_range, func_BitRange, 1);
FMAP_OP(func_get_bit, func_GetBit, 1);

#define FMAP_CSTR(fname, args, from) \
  F_Z3_EXPR_DECL(fname, args) { \
    expr res = fname(EXPAND_ARGS(args, from, S_COMMA)); \
    return z3_expr(z3_cstr(res)); \
  }

FMAP_CSTR(operator<, 2, DATA);
FMAP_CSTR(operator<=, 2, DATA);
FMAP_CSTR(operator>, 2, DATA);
FMAP_CSTR(operator>=, 2, DATA);
FMAP_CSTR(operator==, 2, DATA);
FMAP_CSTR(operator&&, 2, CSTR);
FMAP_CSTR(implies, 2, CSTR);

// ===== Shape   =====

std::vector<int32_t> Shape::ToIndex(size_t index) const {
  VERIFY(0 <= index && index < Size());
  std::vector<int32_t> ret(size());
  for (size_t i = 0; i < size(); ++i) {
    size_t j = size() - 1 - j;
    ret[j] = index % at(j);
    index = index / at(size()-1-i);
  }
  return ret;
}

size_t Shape::Size() const {
  size_t _s = 1;
  for (auto it = begin(); it != end(); ++it) {
    _s *= *it;
  }
  return _s;
}

std::string Shape::to_string() const {
  std::ostringstream oss;
  oss << "(";
  for (auto it = begin(); it != end(); ++it) {
    if (it != begin()) oss << ", ";
    oss << *it;
  }
  oss << ")";
  return oss.str();
}

Shape Shape::from_string(const std::string& st) {
  Shape re;
  int stlen = st.length();
  if (st.length() == 0) {
    return re;
  } else {
    VERIFY(stlen > 1);
  }
  VERIFY((st[0] == '(' && st[stlen-1] == ')') 
      || (st[0] == '[' && st[stlen-1] == ']'));
  for (int i = 1; i < stlen-1; ) {
    std::string num;
    int cnt = 0;
    while ((st[i+cnt] >= '0') && (st[i+cnt] <= '9')) {
      cnt++;
    }
    VERIFY(st[i+cnt] == ',' || st[i+cnt] == ' ' || st[i+cnt] == ')');
    if (cnt > 0) {
      re.emplace_back(std::stoi(st.substr(i, cnt)));
    }
    i = i + (cnt + 1);
  }
  return re;
}

// ===== TypeRef =====

TypePtr TypeRef::Make(
    const std::string &name, 
    const Shape &shape) {
  std::vector<z3_expr> data;
  for (size_t i = 0; i < shape.Size(); ++i) {
    data.emplace_back(name + "_" + std::to_string(i));
  }
  return std::make_shared<TypeRef>(
      TypeRef(data,
        z3_expr(name + "_prec"),
        shape));
}

TypePtr TypeRef::Make(
    const std::string &name, 
    const Shape &shape,
    const z3_expr &prec) {
  std::vector<z3_expr> data;
  for (size_t i = 0; i < shape.Size(); ++i) {
    data.emplace_back(name + "_" + std::to_string(i));
  }
  return std::make_shared<TypeRef>(
      TypeRef(data, prec, shape));
}

TypePtr TypeRef::Make(
    const std::vector<z3_expr> &data,
    const z3_expr &prec,
    const Shape &shape) {
  return std::make_shared<TypeRef>(TypeRef(data, prec, shape));
}

TypePtr TypeRef::copy(const std::string &name) const {
  // TODO(wlt): remove original constraints 
  //  into operator_assertions_.
  TypePtr tr = TypeRef::Make(name, this->shape);
  tr->set_prec(this->prec);
  for (size_t i = 0; i < shape.Size(); ++i) {
    tr->set_data(i, data[i]);
  }
  return tr;
}

void TypeRef::set_data(size_t index, z3_expr const& v) {
  assign_constraints_[index] = (data[index] == v);
  VERIFY(operator_assertions_[index].cstr.is_true())
    << "TypeRef::set_data(): op constraints has been set";
  operator_assertions_[index] = z3_expr(true) && v;
}
void TypeRef::set_prec(z3_expr const& v) {
  assign_constraints_[data.size()] = (prec == v);
  VERIFY(operator_assertions_[data.size()].cstr.is_true())
    << "TypeRef::set_prec(): prec constraints has been set";
  operator_assertions_[data.size()] = z3_expr(true) && v;
}

z3_expr TypeRef::data_constraints() {
  // z3_expr cstr = prec.closed_interval(1, 32);
  z3_expr cstr(true);
  z3_expr r = prec.bit_range();
  for (auto &d : data) {
    cstr = cstr && d.closed_interval(-r, r);
  }
  return cstr;
}
z3_expr TypeRef::data_constraints(size_t index) {
  VERIFY((0 <= index) && (index < data.size()));
  z3_expr const& r = prec.bit_range();
  return data[index].closed_interval(-r, r);
}

z3_expr TypeRef::op_constraints() {
  z3_expr asrt = prec;
  for (const z3_expr &d : data) {
    asrt = asrt && d;
  }
  for (z3_expr const& a : operator_assertions_) {
    asrt = asrt && a;
  }
  return asrt;
}
z3_expr TypeRef::op_constraints(size_t index) {
  return prec && data[index] &&
    operator_assertions_[index];
}

z3_expr TypeRef::prec_constraints() {
  /*
   * Refer to cvm-runtime:src/cvm/infer_attr.cc Line:80
   *  for more details.
   **/
  return prec.closed_interval(1, 32);
}

z3_expr TypeRef::assign_constraints() {
  z3_expr cstr(true);
  for (const auto& c : assign_constraints_) {
    cstr = cstr && c;
  }
  return cstr;
}
z3_expr TypeRef::assign_constraints(size_t index) {
  VERIFY((0 <= index) && (index < data.size()));
  return assign_constraints_[index] &&
    assign_constraints_[data.size()];
}

z3_expr TypeRef::collect_constraints(std::vector<TypePtr> trs) {
  z3_expr cstr(true);
  for (const auto &tr : trs) {
    cstr = cstr &&
      tr->data_constraints() &&
      tr->op_constraints() &&
      tr->prec_constraints() &&
      tr->assign_constraints();
  }
  return cstr;
}

z3_expr TypeRef::deterministic() {
  z3_expr dtmt = prec.deterministic();
  for (auto &d : data) {
    dtmt = dtmt && d.deterministic();
  }
  return dtmt;
}

}
}
