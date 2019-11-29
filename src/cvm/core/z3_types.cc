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

static func_decl func_safe_div() {
  expr a = _Int("a"), b = _Int("b");
  sort I = _IntSort();
  z3::func_decl f = C.recfun("safe_div", I, I, I);
  expr_vector args(C);
  args.push_back(a);
  args.push_back(b);
  C.recdef(f, args,
      z3::ite(b == 0, _IntVal(0), a / b));
  return f;
}
static expr _Div(const expr &a, const expr &b) { 
#if SIMPLIFY_LEVEL <= 4
  static func_decl safe_div = func_safe_div();
  return safe_div(a, b);
#else
  return z3::ite(b == 0, _IntVal(0), a / b);
#endif
}
static expr _Neg(const expr &a) { return -a; }
static expr _Shl(const expr &a) { return z3::shl(1, a); }
/*
 * Must use operator >, since z3::max use bitvector 
 *  unsigned comparation instead of bvsge op.
 **/
static expr _Max(const expr &a, const expr &b) { 
  return z3::ite(a > b, a, b);
 }
static expr _Min(const expr &a, const expr &b) { 
  return z3::ite(a > b, b, a);
}
static expr _Abs(const expr &a) { 
  return z3::ite(a >= 0, a, -a);
}
static expr _Ite(const expr &c, const expr &t, const expr &e) { 
  return z3::ite(c, t, e);
}

static func_decl func_one_shift() {
  expr a = _Int("a"), b = _Int("b");
  sort I = _IntSort();
  z3::func_decl f = C.recfun("one_shift", I, I);
  expr_vector args(C);
  args.push_back(a);
  C.recdef(f, args,
      (z3::shl(1, a-1) - 1));
  return f;
}
static expr _OneShift(const expr &a) {
  static func_decl one_shift = func_one_shift();
  return one_shift(a);
}

static func_decl func_get_bit() {
  expr a = _Int("a");
  sort I = _IntSort();
  z3::func_decl f = C.recfun("get_bit", I, I);
  expr_vector args(C);
  args.push_back(a);
  C.recdef(f, args,
      z3::ite(a == 0, _IntVal(0), f(z3::ashr(a, 1)) + 1));
  return f;
}
static expr _GetBit(const expr &a) {
  static func_decl get_bit = func_get_bit();
  return get_bit(a);
}

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
static expr _MinCstr(const expr &a, const expr &b) { return _BoolVal(true); }

// Do strong constraints, since positive number may not overflow.
static expr _AbsCstr(const expr &a) { return z3::bvneg_no_overflow(a); }
static expr _OneShiftCstr(const expr &a) { return (0 <= a) && (a <= 32); }
static expr _IteCstr(const expr &c, const expr &t, const expr &e) {
  return _BoolVal(true);
}
static expr _GetBitCstr(const expr &a) { return _BoolVal(true); }

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

z3_expr z3_expr::deterministic() {
  return z3_expr(z3_cstr(
        (-Z3_INT32_MAX <= data) && (data <= Z3_INT32_MAX)));
}
z3_expr z3_expr::closed_interval(z3_expr start, z3_expr end) const {
  return z3_expr(z3_cstr(
        (start.data <= data) && (data <= end.data)));
}

z3_expr z3_expr::bit_range() {
#if SIMPLIFY_LEVEL <= 3
  return one_shift(*this);
#else
  return op_1_shift_left((*this - 1)) - 1;
#endif
}

z3_expr z3_expr::get_bit() {
  return bit_prec(*this);
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
FMAP_OP(op_1_shift_left, Shl, 1);
FMAP_OP(one_shift, OneShift, 1);
FMAP_OP(op_max, Max, 2);
FMAP_OP(op_min, Min, 2);
FMAP_OP(op_abs, Abs, 1);
FMAP_OP(op_ite, Ite, 3);
FMAP_OP(bit_prec, GetBit, 1);

#define FMAP_CSTR(fname, args, from) \
  F_Z3_EXPR_DECL(fname, args) { \
    expr res = fname(EXPAND_ARGS(args, from, S_COMMA)); \
    return z3_expr(z3_cstr(res)); \
  }

FMAP_CSTR(operator<, 2, DATA);
FMAP_CSTR(operator<=, 2, DATA);
FMAP_CSTR(operator==, 2, DATA);
FMAP_CSTR(operator&&, 2, CSTR);
FMAP_CSTR(implies, 2, CSTR);

// ===== Shape   =====

size_t Shape::Size() const {
  size_t _s = 1;
  for (auto it = begin(); it != end(); ++it) {
    _s *= *it;
  }
  return _s;
}

std::string Shape::to_string() const {
  std::ostringstream oss;
  oss << "<";
  for (auto it = begin(); it != end(); ++it) {
    if (it != begin()) oss << ", ";
    oss << *it;
  }
  oss << ">";
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
    const std::string &name, 
    const Shape &shape,
    const z3_expr &prec) {
  TypeRef tr(prec, shape);
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

z3_expr TypeRef::data_constraints() {
  z3_expr cstr = prec.closed_interval(1, 32);
  z3_expr r = prec.bit_range();
  for (auto &d : data) {
    cstr = cstr && d.closed_interval(-r, r);
  }
  return cstr;
}

z3_expr TypeRef::op_constraints() {
  z3_expr asrt = prec;
  for (z3_expr &d : data) {
    asrt = asrt && d;
  }
  return asrt;
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
