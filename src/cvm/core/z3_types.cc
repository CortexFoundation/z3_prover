#include "z3++.h"
#include "z3_api.h"

#include "cvm/z3_types.h"

namespace z3 {
namespace type {

context& Z3Context() {
  static context inst;
  return inst;
}

// We use Int64 as placeholder for data, as
//  data in CVM executor is Int32 placeholder.
static const int32_t _INT_PLACE_HLODER = 64;

expr _Int(std::string name) {
  return C.bv_const(name.c_str(), _INT_PLACE_HLODER);
}
expr _IntVal(int32_t val) {
  return C.bv_val(val, 64);
}
sort _IntSort() {
  return C.bv_sort(_INT_PLACE_HLODER);
}
expr _BoolVal(bool val) {
  return C.bool_val(val);
}

expr _Add(const expr &a, const expr &b) {
  return a + b;
}
expr _Sub(const expr &a, const expr &b) {
  return a - b;
}
expr _Mul(const expr &a, const expr &b) {
  return a * b;
}
expr _Div(const expr &a, const expr &b) {
  return a / b;
}
expr _Neg(const expr &a) {
  return -a;
}
expr _Shl(const expr &a) {
  return z3::shl(1, a);
}

expr _AddCstr(const expr &a, const expr &b) {
  return (z3::bvadd_no_overflow(a, b, true) &&
          z3::bvadd_no_underflow(a, b));
}
expr _SubCstr(const expr &a, const expr &b) {
  return (z3::bvsub_no_underflow(a, b, true) &&
          z3::bvsub_no_overflow(a, b));
}
expr _MulCstr(const expr &a, const expr &b) {
  return (z3::bvmul_no_overflow(a, b, true) &&
          z3::bvmul_no_underflow(a, b));
}
expr _DivCstr(const expr &a, const expr &b) {
  return z3::bvsdiv_no_overflow(a, b);
}
expr _NegCstr(const expr &a) {
  return z3::bvneg_no_overflow(a);
}
expr _ShlCstr(const expr &a) {
  return (0 <= a) && (a <= 31);
}
expr _AssignCstr(const expr &a, const expr &b) {
  return a == b;
}

bool is_expr_true(const expr &a) {
  return (a.is_bool() && a.bool_value());
}


// ===== z3_expr =====
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
static const func_decl _BIT_RANGE_FUNC = _BitRange();
z3_expr z3_expr::bit_range() {
  // return _BIT_RANGE_FUNC(val);
  return one_shift_left((*this - 1)) - 1;
}

z3_expr z3_expr::closed_interval(z3_expr start, z3_expr end) {
  return (start <= *this) && (*this <= end);
}


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
  if (data.size() == 0) return _BoolVal(true);

  z3_expr cstr = prec.assign(t->prec);
  for (size_t i = 0; i < data.size(); ++i) {
    cstr = cstr && data[i].assign(t->data[i]);
  }
  return cstr;
}

z3_expr TypeRef::constraints() {
  if (data.size() ==  0) return _BoolVal(true);

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
