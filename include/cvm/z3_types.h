#ifndef Z3_ATTR_TYPE_H
#define Z3_ATTR_TYPE_H

#include <vector>
#include <memory>
#include <exception>
#include <cmath>

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

#define EXPAND_ARGS_1(f, s...) f(t1)
#define EXPAND_ARGS_2(f, s...) EXPAND_ARGS_1(f, ##s)s f(t2)
#define EXPAND_ARGS_3(f, s...) EXPAND_ARGS_2(f, ##s)s f(t3)
#define EXPAND_ARGS(args, f, s...) CONCAT(EXPAND_ARGS_, args)(f, ##s)

#define S_COMMA ,
#define S_SEMI ;

#define Z3_EXPR_DECL(name) const type::z3_expr &name
#define F_Z3_EXPR_DECL(fname, args) \
  z3_expr fname(EXPAND_ARGS(args, Z3_EXPR_DECL, S_COMMA))

#define DEBUG_STR_(macro) #macro
#define DEBUG_STR(macro) DEBUG_STR_(macro)

static const int32_t 
Z3_INT32_MAX = (int64_t{1} << 31) - 1;

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

inline int GetBit(int64_t size) {
  int prec = 0;
  while (size) {
    prec ++;
    size >>= 1;
  }
  return prec;
}

class z3_expr {
 public:
  z3_data data;
  z3_cstr cstr;

  // Avoid implicit convension
  template<typename T>
  z3_expr(T t) = delete;

  // Initial data
  z3_expr(int num);
  z3_expr(const char *name);
  explicit z3_expr(const std::string &name);
  z3_expr(z3_data data);

  // Initial constraints
  z3_expr(bool flag);
  z3_expr(z3_cstr cstr);

  // Initial both
  z3_expr(z3_data data, z3_cstr cstr);

  /* 
   * All higher level function is wrapper of basic
   *  operator declared in friend function as belows:
   *  +, -, *, /, one_shift, ... etc.
   *
   * Micro `F_Z3_EXPR_DECL` is used for declaration of
   *  basic operator function with z3_expr.
   **/
  // Get constraints in closed interval.
  z3_expr closed_interval(
      const z3_expr &start, 
      const z3_expr &end) const;
  z3_expr deterministic() const;

  // Get the positive range of self representation.
  z3_expr bit_range() const;
  z3_expr get_bit() const;
};

// data operator, will collect constraints auto.
// ARGS_EXPAND(operator+, 2);
F_Z3_EXPR_DECL(operator+, 2);
F_Z3_EXPR_DECL(operator-, 2);
F_Z3_EXPR_DECL(operator-, 1);
F_Z3_EXPR_DECL(operator*, 2);
F_Z3_EXPR_DECL(operator/, 2);
F_Z3_EXPR_DECL(operator<<, 2);
F_Z3_EXPR_DECL(operator>>, 2);
F_Z3_EXPR_DECL(op_one_shl, 1);
F_Z3_EXPR_DECL(op_max, 2);
F_Z3_EXPR_DECL(op_min, 2);
F_Z3_EXPR_DECL(op_ite, 3);
F_Z3_EXPR_DECL(op_abs, 1);

F_Z3_EXPR_DECL(func_bit_range, 1);
F_Z3_EXPR_DECL(func_get_bit, 1);

// generate constraints
F_Z3_EXPR_DECL(operator<, 2);
F_Z3_EXPR_DECL(operator<=, 2);
F_Z3_EXPR_DECL(operator>, 2);
F_Z3_EXPR_DECL(operator>=, 2);
F_Z3_EXPR_DECL(operator==, 2);
F_Z3_EXPR_DECL(operator&&, 2);
F_Z3_EXPR_DECL(implies, 2);

// typedef std::vector<int32_t> Shape;
typedef std::vector<int32_t> _ShapeBase;
class Shape : public _ShapeBase {
 public:
  template<typename DIM_T>
  Shape(std::initializer_list<DIM_T> const& init) 
      : _ShapeBase(init) { }

  Shape() : _ShapeBase() {}

  inline bool operator==(Shape const& shp) const {
    return std::equal(begin(), end(), shp.begin());
  }
  inline bool operator!=(Shape const& shp) const {
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

  inline size_t ndim() const {
    return shape.size();
  }
  inline z3_expr asscalar() {
    VERIFY(shape.empty())
      << "TypeRef is not scalar";
    return data[0];
  }
  inline const z3_expr& at(size_t index) const {
    VERIFY((0 <= index) && (index < data.size()))
      << "Index " << index 
      << " out of TypeRef size " << data.size();
    return data[index];
  }
  // inline z3_expr& at(size_t index) {
  //   return const_cast<z3_expr&>(
  //       static_cast<const TypeRef&>(*this).at(index)
  //   );
  // }
  inline size_t Size() const { return shape.Size(); }

  /*
   * TypeRef copy operator inherits current data internal
   *  and precision's constraints and stores into 
   *  operator_assertions_ preparing for further processing,
   *  then create new z3_data symbol and set up assign 
   *  constraints between old and new z3_data.
   **/
  TypePtr copy(const std::string&) const;
  void set_data(size_t index, z3_expr const&);
  void set_prec(z3_expr const&);

  /*
   * TypeRef data constraints are that the data internal 
   *  satisfied the precision range, which means
   *  data between in range [-r, r] where r equals 
   *  with (1 << (prec - 1) - 1.
   **/
  z3_expr data_constraints();
  z3_expr data_constraints(size_t index);
  /*
   * TypeRef precision constraints are that
   *  the precision is in range of [1, 32].
   **/
  z3_expr prec_constraints();
  /*
   * TypeRef op constraints are that the data internal
   *  and precision variables constraints collection, 
   *  which may be by-product that the operator 
   *  processor generated.
   **/
  z3_expr op_constraints();
  z3_expr op_constraints(size_t index);
  /*
   * TypeRef assign constraints are introduced in 
   *  copy function.
   **/
  z3_expr assign_constraints();
  z3_expr assign_constraints(size_t index);
  static z3_expr collect_constraints(std::vector<TypePtr> trs);

  z3_expr deterministic();

  static TypePtr Make(const std::string &name, const Shape &shape);
  // TODO(wlt): using assign constraints by default
  //            for parameters prec and data.
  static TypePtr Make(
      const std::string &name, 
      const Shape &shape,
      const z3_expr &prec);
  static TypePtr Make(
      const std::vector<z3_expr> &data, 
      const z3_expr &prec,
      const Shape &shape);

  // copy constructor use default.
  TypeRef(const TypeRef &t) = default;
  // assign constructor is deleted.
  TypeRef& operator=(const TypePtr &t) = delete;

 protected:
  std::vector<z3_expr> data;
  /*
   * Assign constraints is special, it's different 
   *  from another constraints such operator limit,
   *  it's a easy-and-trick method for proving 
   *  the deterministic of model directed acyclic graph.
   *
   * Assign constraints is recursive collected.
   **/
  std::vector<z3_expr> assign_constraints_;
  std::vector<z3_expr> operator_assertions_;

  inline TypeRef(
      const std::vector<z3_expr> &data,
      const z3_expr &prec, 
      const Shape &shp) : 
      data(data), prec(prec), shape(shp) {
    VERIFY_EQ(shp.Size(), data.size())
      << "TypeRef initializing with non consistent "
      << "shape & data size "
      << shp.to_string() << "==" << shp.Size()
      << " vs. " << data.size();
    assign_constraints_.resize(shp.Size() + 1, z3_expr(true));
    operator_assertions_.resize(shp.Size() + 1, z3_expr(true));
  }
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
  static TypePtr Make(const std::string &name, int data) {
    int abs = data > 0 ? data : -data;
    int bit = (abs > 0) ? log2(double(abs)) + 2 : 1;
    return TypeRef::Make(
        { z3_expr(data) }, z3_expr(bit), {});
  }
  static TypePtr Make(const z3_expr &v, const z3_expr &p) {
    return TypeRef::Make({v}, p, {});
  }
};

}
}

#endif // Z3_ATTR_TYPE_H
