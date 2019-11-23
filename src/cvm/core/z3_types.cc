#include "z3++.h"
#include "z3_api.h"

#include "cvm/base.h"
#include "cvm/z3_types.h"

namespace z3 {
namespace type {

context& Z3Context() {
  static context inst;
  return inst;
}

/*
 * Internal z3 expr helper functions:
 *  1. deterministic data representation creator,
 *    as BitVector of 64 bits and bool value.
 *
 *  2. deterministic data operation function,
 *    contains addition, subtraction, multiply,
 *    division, negative, one_shift_left_bit and
 *    assign operator.
 *
 *  3. other helper function.
 *
 **/

// We use Int64 as placeholder for data, as
//  data in CVM executor is Int32 placeholder.
static const int32_t _INT_PLACE_HOLDER = 64;

static expr _Int(const char *n) { return C.bv_const(n, _INT_PLACE_HOLDER); }
static expr _Int(const std::string &n) { return _Int(n.c_str()); }
static expr _IntVal(int32_t val) { return C.bv_val(val, 64); }
static bool _IsInt(expr val) { return val.is_bv(); }
static sort _IntSort() { return C.bv_sort(_INT_PLACE_HOLDER); }
static expr _BoolVal(bool val) { return C.bool_val(val); }
static bool _IsBool(expr val) { return val.is_bool(); }

static expr _Add(const expr &a, const expr &b) { return a + b; }
static expr _Sub(const expr &a, const expr &b) { return a - b; }
static expr _Mul(const expr &a, const expr &b) { return a * b; }
static expr _Div(const expr &a, const expr &b) { return a / b; }
static expr _Neg(const expr &a) { return -a; }
static expr _Shl(const expr &a) { return z3::shl(1, a); }
static expr _Max(const expr &a, const expr &b) { return z3::max(a, b); }

static expr _AddCstr(const expr &a, const expr &b) {
  return (z3::bvadd_no_overflow(a, b, true) &&
          z3::bvadd_no_underflow(a, b)); 
}
static expr _SubCstr(const expr &a, const expr &b) {
  return (z3::bvsub_no_underflow(a, b, true) &&
          z3::bvsub_no_overflow(a, b)); 
}
static expr _MulCstr(const expr &a, const expr &b) {
  return (z3::bvmul_no_overflow(a, b, true) &&
          z3::bvmul_no_underflow(a, b)); 
}
static expr _DivCstr(const expr &a, const expr &b) { 
  return z3::bvsdiv_no_overflow(a, b); 
}
static expr _NegCstr(const expr &a) { return z3::bvneg_no_overflow(a); }
static expr _ShlCstr(const expr &a) { return (0 <= a) && (a <= 31); }
static expr _MaxCstr(const expr &a, const expr &b) { return _BoolVal(true); }

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
  const expr &a_sim = a.simplify();
  const expr &b_sim = b.simplify();
  if (a_sim.is_true()) return b;
  else if (b_sim.is_true()) return a;
  else if (a_sim.is_false() || b_sim.is_false()) 
    return _BoolVal(false);
  return z3::operator&&(a, b);
}

z3_cstr operator||(const z3_cstr &a, const z3_cstr &b) {
  const expr &a_sim = a.simplify();
  const expr &b_sim = b.simplify();
  if (a_sim.is_false()) return b;
  else if (b_sim.is_false()) return a;
  else if (a_sim.is_true() || b_sim.is_true())
    return _BoolVal(true);
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

static const int32_t _INT32_MAX = (int64_t{1} << 31) - 1;
z3_expr z3_expr::deterministic() {
  return z3_expr(z3_cstr(
        (-_INT32_MAX <= data) && (data <= _INT32_MAX)));
}
z3_expr z3_expr::closed_interval(z3_expr start, z3_expr end) {
  return z3_expr(z3_cstr(
        (start.data <= data) && (data <= end.data)));
}

/*
 * func_decl _BitRange() {
 *   expr a = _Int("a"), b = _Int("b");
 *   sort I = _IntSort();
 *   z3::func_decl f = C.recfun("bit_range", I, I);
 *   expr_vector args(C);
 *   args.push_back(a);
 *   C.recdef(f, args,
 *       (z3::shl(1, a-1) - 1));
 *   return f;
 * }
 * static const func_decl _BIT_RANGE_FUNC = _BitRange();
 **/
z3_expr z3_expr::bit_range() {
  // return _BIT_RANGE_FUNC(val);
  return op_1_shift_left((*this - 1)) - 1;
}

#define FVAL_1(__data) t1.__data
#define FVAL_2(__data) FVAL_1(__data), t2.__data

#define AND_1() c = c && t1.cstr;
#define AND_2() AND_1(); c = c && t2.cstr;

#define FMAP_OP(__f, __op, __args) \
  FEXPR_MAP_DECL(__f, __args) { \
    z3_data v = _ ## __op(CONCAT(FVAL_, __args)(data));     \
    z3_cstr c = _ ## __op ## Cstr(CONCAT(FVAL_, __args)(data)); \
    CONCAT(AND_, __args)(); \
    return z3_expr(v, c); \
  }

FMAP_OP(operator+, Add, 2);
FMAP_OP(operator-, Sub, 2);
FMAP_OP(operator-, Neg, 1);
FMAP_OP(operator*, Mul, 2);
FMAP_OP(operator/, Div, 2);
FMAP_OP(op_1_shift_left, Shl, 1);
FMAP_OP(op_max, Max, 2);

#define FMAP_CSTR(__f, __args, __from) \
  FEXPR_MAP_DECL(__f, __args) { \
    expr res = __f(CONCAT(FVAL_, __args)(__from)); \
    return z3_expr(z3_cstr(res)); \
  }

FMAP_CSTR(operator<, 2, data);
FMAP_CSTR(operator<=, 2, data);
FMAP_CSTR(operator==, 2, data);
FMAP_CSTR(operator&&, 2, cstr);
FMAP_CSTR(implies, 2, cstr);

// ===== Shape   =====

size_t Shape::Size() const {
  size_t _s = 1;
  for (auto it = this->begin(); it != this->end(); ++it) {
    _s *= *it;
  }
  return _s;
}

std::string Shape::to_string() const {
  std::ostringstream oss;
  oss << "< ";
  for (auto it = begin(); it != end(); ++it) {
    if (it != begin()) oss << ", ";
    oss << *it;
  }
  return oss.str();
}

// ===== TypeRef =====

TypePtr TypeRef::Make(
    const std::string &name, 
    const Shape &shape) {
  TypeRef tr(z3_expr(name + "_prec"), shape);
  for (size_t i = 0; i < shape.Size(); ++i) {
    tr.data.emplace_back(name + "_" + std::to_string(i));
  }
  return std::make_shared<TypeRef>(tr);
}

TypePtr TypeRef::Make(
    const std::vector<z3_expr> &data,
    const z3_expr &prec,
    const Shape &shape) {
  VERIFY_EQ(shape.Size(), data.size())
    << "Shape " << shape.to_string() << " is not consistent with "
    << "data size " << data.size();

  TypeRef tr(prec, shape);
  tr.data = data;
  return std::make_shared<TypeRef>(tr);
}

z3_expr TypeRef::assign(const TypePtr &t) {
  VERIFY_EQ(t->shape, shape) << "TypeRef assig error";

  z3_expr cstr = (prec == t->prec);
  for (size_t i = 0; i < data.size(); ++i) {
    cstr = cstr && (data[i] == t->data[i]);
  }
  return cstr;
}

z3_expr TypeRef::constraints() {
  z3_expr cstr = prec.closed_interval(1, 32);
  z3_expr r = prec.bit_range();
  for (auto &d : data) {
    cstr = cstr && d.closed_interval(-r, r);
  }
  return cstr;
}

z3_expr TypeRef::assertions() {
  z3_expr asrt = prec;
  for (z3_expr &d : data) {
    asrt = asrt && d;
  }
  return asrt;
}

}
}
