#ifndef Z3_ATTR_TYPE_H
#define Z3_ATTR_TYPE_H

#include <vector>
#include <memory>
#include <exception>

#include "z3++.h"

namespace z3 {
namespace type {

class TypeRef;
using TypePtr = std::shared_ptr<TypeRef>;

context& Z3Context();
#define C Z3Context()

// Helper function for Z3 Data type creator.
expr _Int(std::string name);
expr _IntVal(int32_t val);
expr _BoolVal(bool b);

// Helper function for Z3-Int data type operation,
//  and we suppose the basic mathmatic operation is deterministic
expr _Add(const expr &a, const expr &b);
expr _Sub(const expr &a, const expr &b);
expr _Mul(const expr &a, const expr &b);
expr _Div(const expr &a, const expr &b);
expr _Neg(const expr &a);
expr _Shl(const expr &a);

expr _AddCstr(const expr &a, const expr &b);
expr _SubCstr(const expr &a, const expr &b);
expr _MulCstr(const expr &a, const expr &b);
expr _DivCstr(const expr &a, const expr &b);
expr _NegCstr(const expr &a);
expr _ShlCstr(const expr &a);
expr _AssignCstr(const expr &a, const expr &b);

bool is_expr_true(const expr &e);

#define CONCAT_(a, b) a ## b
#define CONCAT(a, b) CONCAT_(a, b)

#define FARG_1() const z3_expr &t1
#define FARG_2() FARG_1(), const z3_expr &t2
#define FVAL_1() t1.val
#define FVAL_2() FVAL_1(), t2.val

#define FMAP_OP(__f, __op, __args) \
  inline z3_expr __f(CONCAT(FARG_, __args)()) { \
    expr v = _ ## __op(CONCAT(FVAL_, __args)());     \
    expr c = _ ## __op ## Cstr(CONCAT(FVAL_, __args)()); \
    if (!is_expr_true(t1.cstr)) { \
      c = t1.cstr && c; \
    } \
    return z3_expr(v, c); \
  }

#define FMAP(__f, __args) \
  inline z3_expr __f(CONCAT(FARG_, __args)()) { \
    return z3_expr(z3::__f(CONCAT(FVAL_, __args)())); \
  }

#define FRENAME(__old, __new, __args) \
  inline z3_expr __new(CONCAT(FARG_, __args)()) { \
    return z3_expr(__old(CONCAT(FVAL, __args)())) \
  }

class z3_expr {
 public:
  expr val;
  expr cstr;

  z3_expr(std::string name) :
    val(_Int(name)), cstr(_BoolVal(true)) {}
  z3_expr(int num) :
    val(_IntVal(num)), cstr(_BoolVal(true)) {}
  z3_expr(expr val) :
    val(val), cstr(_BoolVal(true)) {}
  z3_expr(expr val, expr cstr) :
    val(val), cstr(cstr) {}

  inline z3_expr assign(const z3_expr &t) {
    return _AssignCstr(val, t.val);
  }

  z3_expr closed_interval(z3_expr start, z3_expr end);
  z3_expr bit_range();
};

FMAP_OP(operator+, Add, 2);
FMAP_OP(operator-, Sub, 2);
FMAP_OP(operator-, Neg, 1);
FMAP_OP(operator*, Mul, 2);
FMAP_OP(operator/, Div, 2);
FMAP_OP(one_shift_left, Shl, 1);

FMAP(max, 2);
FMAP(operator<, 2);
FMAP(operator<=, 2);
FMAP(operator&&, 2);

static const int32_t 
_INT32_MAX = (int64_t{1} << 31) - 1;

class TypeRef {
 public:
  std::vector<z3_expr> data;
  z3_expr prec;

  // Shape indicates the orginization structure of data, 
  //  which equals with data.size().
  std::vector<int32_t> shape; 

  inline z3_expr asscalar() {
    if (data.size() == 1) {
      return data[0];
    }

    throw std::runtime_error("TypeRef is not scalar.");
  }

  /*
   * Copy current TypeRef's shape and data placeholder 
   *  into new one, which indicates that the real expression
   *  stored is not copied.
   **/
  TypePtr copy_placeholder(std::string name);

  /*
   * Basic operation constraints
   **/
  z3_expr assign(const TypePtr &t);

  /*
   * Collect current stored data's constriants.
   **/
  z3_expr constraints();

  inline z3_expr operator[](size_t index) {
    return data[index];
  }

 protected:
  TypeRef(z3_expr prec) : prec(prec) {}
};

/*
 * Scalar's shape is empty, which is (), named as scalar.
 *  It's data only contains single z3_expr.
 **/
class Scalar final : public TypeRef {
 public:
  static TypePtr Make(const std::string &name) {
    return std::make_shared<Scalar>(Scalar(name));
  }
  static TypePtr Make(const std::string &name, int prec) {
    return std::make_shared<Scalar>(Scalar(name, prec));
  }

  static TypePtr Make(const z3_expr &v, const z3_expr &p) {
    return std::make_shared<Scalar>(Scalar(v, p));
  }

 private:
  Scalar(const std::string &name) :
    TypeRef("p_"+name) 
  {
    data.emplace_back(name);
  }
  Scalar(const std::string &name, int prec) :
    TypeRef(prec) 
  {
    data.emplace_back(name);
  }
  Scalar(const z3_expr &v, const z3_expr &p) :
    TypeRef(p) 
  {
    data.emplace_back(v);
  }
};

}
}

#endif // Z3_ATTR_TYPE_H
