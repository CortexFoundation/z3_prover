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

static const int32_t 
_INT32_MAX = (int32_t{1} << 31) - 1;

class IntPrim {    // Z3 Int Primitive
 public:
  IntPrim(expr v, expr p) : 
    val(v), prec(p) {}

  IntPrim(std::string name) :
    val(C.int_const(name.c_str())),
    prec(C.int_const(("p_"+name).c_str())) 
  {}

  inline expr constraints() {
    expr r = BitRange(prec);
    return InClosedInterval(prec, 1, 32) &&
           InClosedInterval(val, -r, r);
  }

  inline expr assign_constraints(const IntPrim &t) {
    return ((t.val == val) && (t.prec == prec));
  }

  inline expr deterministic() {
    return InClosedInterval(val, -_INT32_MAX, _INT32_MAX);
  }

  expr val;         // data value
  expr prec;        // data precision
};

class TypeRef {
  // TODO(wlt): Assign operator
 public:
  inline IntPrim asscalar() {
    if (data_.size() == 1) {
      return data_[0];
    }

    throw std::runtime_error("TypeRef is not scalar.");
  }

  inline TypePtr copy(std::string name) {
    TypeRef cp;
    for (size_t i = 0; i < this->data_.size(); ++i) {
      cp.data_.push_back(IntPrim(name+"_"+std::to_string(i)));
    }
    cp.shape_ = this->shape_;
    return std::make_shared<TypeRef>(cp);
  }

  inline expr assign_constraints(const TypePtr &t) {
    if (t->data_.size() != data_.size()) {
      throw std::runtime_error("TypeRef assign error");
    }
    if (data_.size() == 0) return C.bool_val(true);

    expr cstr = data_[0].assign_constraints(t->data_[0]);
    for (size_t i = 1; i < data_.size(); ++i) {
      cstr = cstr && data_[i].assign_constraints(t->data_[i]);
    }
    return cstr;
  }

  inline expr constraints() {
    if (data_.size() ==  0) return C.bool_val(true);

    expr cstr = data_[0].constraints();
    for (size_t i = 1; i < data_.size(); ++i) 
      cstr = cstr && data_[i].constraints();
    return cstr;
    // return (C.bool_val(false) || cstr);
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
  std::vector<int32_t> shape_;

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
    // shape is ()
  }

  explicit Scalar(expr v, expr p) {
    data_.emplace_back(IntPrim(v, p));
    // shape is ()
  
  }
};

}
}

#endif // Z3_ATTR_TYPE_H
