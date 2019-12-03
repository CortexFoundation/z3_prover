#ifndef Z3_FUNC_H
#define Z3_FUNC_H

#include "z3++.h"
#include "cvm/z3_types.h"

namespace z3 {
namespace type {

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

/*
 * Helper function defined in z3_func mode.
 **/
static func_decl func_bit_range() {
  expr a = _Int("a"), b = _Int("b");
  sort I = _IntSort();
  z3::func_decl f = C.recfun("bit_range", I, I);
  expr_vector args(C);
  args.push_back(a);
  C.recdef(f, args,
      (z3::shl(1, a-1) - 1));
  return f;
}

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

/*
 * Wrapper function for z3 operator such as +,-,*,/ ...etc.
 *  And generating consistent constraints binding into
 *  the operator.
 **/

static expr _Add(const expr &a, const expr &b) { return a + b; }
static expr _Sub(const expr &a, const expr &b) { return a - b; }
static expr _Mul(const expr &a, const expr &b) { return a * b; }
static expr _Div(const expr &a, const expr &b) { 
#if SIMPLIFY_LEVEL <= 4
  static func_decl safe_div = func_safe_div();
  return safe_div(a, b);
#else
  return z3::ite(b == 0, _IntVal(0), a / b);
#endif
}
static expr _Neg(const expr &a) { return -a; }


static expr _OneShl(const expr &a) { return z3::shl(1, a); }
static expr _Shr(const expr &a, const expr &b) { return z3::ashr(a, b); }
static expr _Shl(const expr &a, const expr &b) { return z3::shl(a, b); }

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

static expr _func_BitRange(const expr &a) {
  static func_decl one_shift = func_bit_range();
  return one_shift(a);
}

static expr _func_GetBit(const expr &a) {
  static func_decl get_bit = func_get_bit();
  return get_bit(a);
}

/*
 * All operator constraints is to avoid overflow or underflow.
 **/
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

static expr _OneShlCstr(const expr &a) { return (0 <= a) && (a <= 31); }
static expr _ShrCstr(const expr &a, const expr &b) {
  return (0 <= b) && (b <= 31);
}
static expr _ShlCstr(const expr &a, const expr &b) {
  return (-Z3_INT32_MAX <= a) && (a <= Z3_INT32_MAX) &&
    (0 <= b) && (b <= 31);
}
static expr _MaxCstr(const expr &a, const expr &b) { return _BoolVal(true); }
static expr _MinCstr(const expr &a, const expr &b) { return _BoolVal(true); }

// Do strong constraints, since positive number may not overflow.
static expr _AbsCstr(const expr &a) { return z3::bvneg_no_overflow(a); }
static expr _IteCstr(const expr &c, const expr &t, const expr &e) {
  return _BoolVal(true);
}

static expr _func_BitRangeCstr(const expr &a) { 
  return (0 <= a) && (a <= 32); 
}
static expr _func_GetBitCstr(const expr &a) { return _BoolVal(true); }


}
}

#endif // Z3_FUNC_H
