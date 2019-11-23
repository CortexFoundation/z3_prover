#ifndef Z3_ATTR_TYPE_H
#define Z3_ATTR_TYPE_H

#include <vector>
#include <memory>
#include <exception>

#include "z3++.h"
#include "base.h"

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
  // Avoid implicit convension
  template<typename T>
  z3_data(T t) = delete;

  z3_data(int num = 0);
  z3_data(const char *name);
  z3_data(const std::string &name);
  z3_data(expr val);
};

class z3_cstr : public expr {
 public:
  // Avoid implicit convension
  template<typename T>
  z3_cstr(T t) = delete;

  z3_cstr();
  z3_cstr(expr cstr);
};

z3_cstr operator&&(const z3_cstr&, const z3_cstr&);
z3_cstr operator||(const z3_cstr&, const z3_cstr&);

class z3_expr {
 public:
  z3_data data;
  z3_cstr cstr;

  // Avoid implicit convension
  template<typename T>
  z3_expr(T t) = delete;

  // initial data
  z3_expr(int num);
  z3_expr(const char *name);
  z3_expr(const std::string &name);
  z3_expr(z3_data data);

  // initial constraints
  z3_expr(bool flag);
  z3_expr(z3_cstr cstr);

  // initial both
  z3_expr(z3_data data, z3_cstr cstr);

  // get constraints in closed interval.
  z3_expr closed_interval(z3_expr start, z3_expr end);
  z3_expr deterministic();

  // get the positive range of self representation.
  z3_expr bit_range();
};

// data operator, will collect constraints auto.
FEXPR_MAP_DECL(operator+, 2);
FEXPR_MAP_DECL(operator-, 2);
FEXPR_MAP_DECL(operator-, 1);
FEXPR_MAP_DECL(operator*, 2);
FEXPR_MAP_DECL(operator/, 2);
FEXPR_MAP_DECL(op_1_shift_left, 1);
FEXPR_MAP_DECL(op_max, 2);

// generate constraints
FEXPR_MAP_DECL(operator<, 2);
FEXPR_MAP_DECL(operator<=, 2);
FEXPR_MAP_DECL(operator==, 2);
FEXPR_MAP_DECL(operator&&, 2);
FEXPR_MAP_DECL(implies, 2);

// typedef std::vector<int32_t> Shape;
class Shape : public std::vector<int32_t> {
 public:
  Shape(std::initializer_list<int32_t> init) 
      : std::vector<int32_t>(init) { }

  inline bool operator==(const Shape &shp) const {
    return std::equal(begin(), end(), shp.begin());
  }
  inline bool operator!=(const Shape &shp) const {
    return !(*this == shp);
  }

  size_t Size() const;
  std::string to_string() const;
};

class TypeRef {
 public:
  z3_expr prec;

  // Shape indicates the orginization structure of data, 
  //  which equals with data.size().
  const Shape shape; 

  inline z3_expr asscalar() {
    VERIFY(shape.empty())
      << "TypeRef is not scalar";
    return data[0];
  }
  inline z3_expr at(size_t index) const {
    VERIFY((0 <= index) && (index < data.size()))
      << "Index " << index 
      << " out of TypeRef size " << data.size();
    return data[index];
  }

  /*
   * Basic operation constraints
   **/
  z3_expr assign(const TypePtr &t);

  /*
   * Collect current stored data's constriants.
   **/
  z3_expr constraints();

  z3_expr assertions();

  static TypePtr Make(const std::string &name, const Shape &shape);
  static TypePtr Make(
      const std::vector<z3_expr> &data, 
      const z3_expr &prec,
      const Shape &shape);

 protected:
  std::vector<z3_expr> data;

  TypeRef(const z3_expr &prec, const Shape &shp) : 
    prec(prec), shape(shp) {}
};

/*
 * Scalar's shape is empty, which is (), named as scalar.
 *  It's data only contains single z3_expr.
 **/
class Scalar final : public TypeRef {
 public:
  static TypePtr Make(const std::string &name) {
    return TypeRef::Make(name, {});
  }
  static TypePtr Make(
      const z3_expr &v, const z3_expr &p) {
    return TypeRef::Make({v}, p, {});
  }
};

}
}

#endif // Z3_ATTR_TYPE_H
