#include "z3++.h"
#include "z3_api.h"

#include "cvm/z3_types.h"

namespace z3 {
namespace utils {

bool is_expr_true(const expr &a) {
  return (a.is_bool() && a.bool_value());
}

}
}

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

static expr _Int(std::string name) { 
  return C.bv_const(name.c_str(), _INT_PLACE_HOLDER); 
}
static expr _IntVal(int32_t val) { return C.bv_val(val, 64); }
static sort _IntSort() { return C.bv_sort(_INT_PLACE_HOLDER); }
static expr _BoolVal(bool val) { return C.bool_val(val); }

static expr _Add(const expr &a, const expr &b) { return a + b; }
static expr _Sub(const expr &a, const expr &b) { return a - b; }
static expr _Mul(const expr &a, const expr &b) { return a * b; }
static expr _Div(const expr &a, const expr &b) { return a / b; }
static expr _Neg(const expr &a) { return -a; }
static expr _Shl(const expr &a) { return z3::shl(1, a); }

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
static expr _NegCstr(const expr &a) { 
  return z3::bvneg_no_overflow(a); 
}
static expr _ShlCstr(const expr &a) {
  return (0 <= a) && (a <= 31);
}

// ===== z3 data & cstr =====

z3_data::z3_data(int num) : expr(_IntVal(num)) {}
z3_data::z3_data(std::string name) : expr(_Int(name)) {}
z3_data::z3_data(expr val) : expr(val) {
  if (val.is_bool()) {
    this->~z3_data(); // Free resource.
    throw std::runtime_error(
        "z3_data " + val.to_string() + " is non data");
  }
}

static const int32_t _INT32_MAX = (int64_t{1} << 31) - 1;
z3_cstr z3_data::deterministic() {
  return (-_INT32_MAX <= *this) && (*this <= _INT32_MAX);
}

z3_cstr::z3_cstr() : expr(_BoolVal(true)) {}
z3_cstr::z3_cstr(expr val) : expr(val) { 
  if (!val.is_bool()) {
    this->~z3_cstr(); // Free resource.
    throw std::runtime_error(
        "z3_cstr " + val.to_string() + " is non constraints");
  }
}

z3_cstr operator&&(const z3_cstr &a, const z3_cstr &b) {
  if (a.is_true()) return b;
  else if (b.is_true()) return a;
  return a && b;
}

z3_cstr operator||(const z3_cstr &a, const z3_cstr &b) {
  if (a.is_false()) return b;
  else if (b.is_false()) return a;
  return a || b;
}

// ===== z3_expr =====

z3_expr::z3_expr(std::string name) : data(name) {}
z3_expr::z3_expr(int num) : data(num) {}
z3_expr::z3_expr(bool flag): cstr(_BoolVal(flag)) {}
z3_expr::z3_expr(z3_data data) : data(data) {}
z3_expr::z3_expr(z3_cstr cstr) : cstr(cstr) {}
z3_expr::z3_expr(z3_data data, z3_cstr cstr) :
  data(data), cstr(cstr) {}

// func_decl _BitRange() {
//   expr a = _Int("a"), b = _Int("b");
//   sort I = _IntSort();
//   z3::func_decl f = C.recfun("bit_range", I, I);
//   expr_vector args(C);
//   args.push_back(a);
//   C.recdef(f, args, 
//       (z3::shl(1, a-1) - 1));
//   return f;
// }
// static const func_decl _BIT_RANGE_FUNC = _BitRange();
z3_expr z3_expr::bit_range() {
  // return _BIT_RANGE_FUNC(val);
  return op_1_shift_left((*this - 1)) - 1;
}

z3_expr z3_expr::closed_interval(z3_expr start, z3_expr end) {
  return (start <= *this) && (*this <= end);
}

#define FVAL_1(__data) t1.__data
#define FVAL_2(__data) FVAL_1(__data), t2.__data

#define AND_1() c = c && t1.cstr;
#define AND_2() AND_1(); c = c && t2.cstr;

#define FOP_DEF(__f, __op, __args) \
  FEXPR_MAP_DECL(__f, __args) { \
    z3_data v = _ ## __op(CONCAT(FVAL_, __args)(data));     \
    z3_cstr c = _ ## __op ## Cstr(CONCAT(FVAL_, __args)(cstr)); \
    CONCAT(AND_, __args)(); \
    return z3_expr(v, c); \
  }

FOP_DEF(operator+, Add, 2);
FOP_DEF(operator-, Sub, 2);
FOP_DEF(operator-, Neg, 1);
FOP_DEF(operator*, Mul, 2);
FOP_DEF(operator/, Div, 2);
FOP_DEF(op_1_shift_left, Shl, 1);

#define FMAP_EXPR(__f, __args, __from, __to) \
  FEXPR_MAP_DECL(__f, __args) { \
    expr res = z3::__f(CONCAT(FVAL_, __args)(__from)); \
    return z3_expr(CONCAT(z3_, __to)(res)); \
  }

// TODO(wlt): function generating data should collect constraints?
FMAP_EXPR(max, 2, data, data);
FMAP_EXPR(operator<, 2, data, cstr);
FMAP_EXPR(operator<=, 2, data, cstr);
FMAP_EXPR(operator==, 2, data, cstr);
FMAP_EXPR(operator&&, 2, cstr, cstr);

// ===== TypeRef =====

TypePtr TypeRef::copy_placeholder(std::string name) {
  TypeRef cp(prec);
  for (size_t i = 0; i < this->data.size(); ++i) {
    cp.data.emplace_back( name+"_"+std::to_string(i) );
  }
  cp.shape = this->shape;
  return std::make_shared<TypeRef>(cp);
}

z3_expr TypeRef::assign(const TypePtr &t) {
  if (t->data.size() != data.size()) {
    throw std::runtime_error("TypeRef assign error");
  }
  if (data.size() == 0) return z3_expr(true);

  z3_expr cstr = (prec == t->prec);
  for (size_t i = 0; i < data.size(); ++i) {
    cstr = cstr && (data[i] == t->data[i]);
  }
  return cstr;
}

z3_expr TypeRef::constraints() {
  if (data.size() ==  0) return z3_expr(true);

  z3_expr cstr = prec.closed_interval(1, 32);
  z3_expr r = prec.bit_range();
  for (auto &d : data) {
    cstr = cstr && d.closed_interval(-r, r);
  }
  return cstr;
  // return (_BoolVal(false) || cstr);
}

}
}
