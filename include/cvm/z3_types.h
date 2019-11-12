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

expr InClosedInterval(expr x, expr start, expr end);
expr InClosedInterval(expr x, int start, int end);
expr BitRange(expr prec);

static const int _INT32_MAX = z3::pw(C.int_val(2), 31) - 1;
class IntPrim {    // Z3 Int Primitive
 public:
  IntPrim(expr v = expr(C),
          expr p = expr(C))
    : val(v), prec(p)
    {}

  inline expr constraints() {
    expr r = BitRange(prec);
    std::cout << (val <= r) << std::endl;
    return InClosedInterval(prec, 1, 32) &&
           InClosedInterval(val, -r, r);
  }

  inline expr deterministic() {
    return InClosedInterval(val, -_INT32_MAX, _INT32_MAX);
  }

  expr val;         // data value
  expr prec;        // data precision
};

class TypeRef {
 public:
  inline IntPrim asscalar() {
    if (data_.size() == 1) {
      return data_[0];
    }

    throw std::runtime_error("TypeRef is not scalar.");
  }

  inline expr constraints() {
    expr cstr = C.bool_val(true);
    for (IntPrim &d : data_) {
      cstr = cstr && d.constraints();
    }
    return cstr;
  }

  inline expr deterministic() {
    expr dmst = C.bool_val(true);
    for (IntPrim &d : data_) {
      dmst = dmst && d.deterministic();
    }
    return dmst;
  }

  IntPrim operator[](size_t index) {
    return data_[index];
  }

 protected:
  std::vector<IntPrim> data_;

  TypeRef() = default;
};

class Scalar final : public TypeRef {
 public:
  static TypePtr Make(std::string name, int prec=-1) {
    return std::make_shared<Scalar>(Scalar(name, prec));
  }

  static TypePtr Make(expr v, expr p) {
    return std::make_shared<Scalar>(Scalar(v, p));
  }

 private:
  explicit Scalar(std::string name, int prec=-1) {
    expr v = C.int_const(name.c_str());
    expr p(C);
    if (prec == -1) {
      p = C.int_const(("p_" + name).c_str());
    } else {
      p = C.int_val(prec);
    }

    data_.emplace_back(IntPrim(v, p));
  }

  explicit Scalar(expr v, expr p) {
    data_.emplace_back(IntPrim(v, p));
  
  }
};

}
}

#endif // Z3_ATTR_TYPE_H
