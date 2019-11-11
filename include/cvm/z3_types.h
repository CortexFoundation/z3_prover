#ifndef Z3_ATTR_TYPE_H
#define Z3_ATTR_TYPE_H

#include <vector>
#include <exception>

#include <z3++.h>

namespace z3 {
namespace type {

context& Z3Context() {
  static context inst;
  return inst;
}
#define C Z3Context()

struct IntPrim {
  IntPrim() :
    name(""),
    val(C),
    prec(C) {} 

  std::string name; // Data name
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

 protected:
  std::vector<IntPrim> data_;
};

class Scalar : TypeRef {
 public:
  Scalar(std::string name, int prec=-1) {
    IntPrim ip;
    ip.val = C.int_const(name.c_str());

    if (prec == -1) {
      ip.prec = C.int_val(prec);
    } else {
      ip.prec = C.int_const(("p_" + name).c_str());
    }

    data_.push_back(std::move(ip));
  }
};

}
}

#endif // Z3_ATTR_TYPE_H
