#ifndef Z3_ATTR_TYPE_H
#define Z3_ATTR_TYPE_H

#include <vector>
#include <memory>
#include <exception>

#include "z3++.h"

namespace z3 {
namespace utils {

bool is_expr_true(const expr &a);

}
}

namespace z3 {
namespace type {

class TypeRef;
using TypePtr = std::shared_ptr<TypeRef>;

context& Z3Context();
#define C Z3Context()


#define CONCAT_(a, b) a ## b
#define CONCAT(a, b) CONCAT_(a, b)

#define FARG_1() const z3_expr &t1
#define FARG_2() FARG_1(), const z3_expr &t2

#define FEXPR_MAP_DECL(__f, __args) \
  z3_expr __f(CONCAT(FARG_, __args)())

class z3_cstr;

class z3_data : public expr {
 public:
  z3_data(int num = 0);
  z3_data(std::string name);
  z3_data(expr val);

  z3_cstr deterministic();
};

class z3_cstr : public expr {
 public:
  z3_cstr();
  z3_cstr(expr cstr);
};

z3_cstr operator&&(const z3_cstr&, const z3_cstr&);
z3_cstr operator||(const z3_cstr&, const z3_cstr&);

class z3_expr {
 public:
  z3_data data;
  z3_cstr cstr;

  z3_expr(std::string name);
  z3_expr(int num);
  z3_expr(bool flag);
  explicit z3_expr(z3_data data);
  explicit z3_expr(z3_cstr cstr);
  explicit z3_expr(z3_data data, z3_cstr cstr);

  // get constraints in closed interval.
  z3_expr closed_interval(z3_expr start, z3_expr end);

  // get the positive range of self representation.
  z3_expr bit_range();
};

FEXPR_MAP_DECL(operator+, 2);
FEXPR_MAP_DECL(operator-, 2);
FEXPR_MAP_DECL(operator-, 1);
FEXPR_MAP_DECL(operator*, 2);
FEXPR_MAP_DECL(operator/, 2);
FEXPR_MAP_DECL(op_1_shift_left, 1);

FEXPR_MAP_DECL(max, 2);
FEXPR_MAP_DECL(operator<, 2);
FEXPR_MAP_DECL(operator<=, 2);
FEXPR_MAP_DECL(operator==, 2);
FEXPR_MAP_DECL(operator&&, 2);

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
