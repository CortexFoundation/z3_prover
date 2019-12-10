#ifndef Z3_CVM_OP_H
#define Z3_CVM_OP_H

#include <memory>
#include <limits>
#include <z3++.h>

#include "base.h"
#include "z3_types.h"
#include "registry.h"

namespace z3 {
namespace cvm {

/*! \brief constant to indicate it take any length of positional inputs */
static const uint32_t kVarg = std::numeric_limits<uint32_t>::max();

struct NodeAttrs;

using func_pg = std::function<
  std::vector<type::z3_expr>()>;

class Op {
 public:
  std::string name;

  uint32_t num_inputs = 1;
  uint32_t num_outputs = 1;

  std::function<uint32_t(const NodeAttrs& attrs)> get_num_outputs = nullptr;
  std::function<uint32_t(const NodeAttrs& attrs)> get_num_inputs = nullptr;

  inline Op& set_num_inputs(uint32_t n) {
    this->num_inputs = n;
    return *this;
  }
  inline Op& set_num_inputs(
      std::function<uint32_t(const NodeAttrs& attr)> fn) {
    this->get_num_inputs = fn;
    return *this;
  }

  inline Op& set_num_outputs(uint32_t n) {
    this->num_outputs = n;
    return *this;
  }
  inline Op& set_num_outputs(
      std::function<uint32_t(const NodeAttrs& attr)> fn) {
    this->get_num_outputs = fn;
    return *this;
  }

  std::function<type::z3_expr(
      const NodeAttrs &attrs,
      std::vector<type::TypePtr> &inputs,
      std::vector<type::TypePtr> &outputs)> 
  forward_func = nullptr;

  inline Op& set_forward(
      std::function<type::z3_expr(
          const NodeAttrs&, 
          std::vector<type::TypePtr>&,
          std::vector<type::TypePtr>&)
      > forward_func) {
    this->forward_func = forward_func;
    return *this;
  }

  func_pg provements_generator = nullptr;

  inline Op& set_generator(
      std::function<std::vector<type::z3_expr>()> func) {
    this->provements_generator = func;
    return *this;
  }

  static const Op* Get(const std::string& op_name);
  static std::vector<std::string> ListAllNames();

 private:
  friend class utils::Registry<Op>;

  uint32_t index_{0};
  Op();
};

#define Z3_REGISTER_VAR_DEF(OpName)                                   \
  static Z3UTIL_ATTRIBUTE_UNUSED ::z3::cvm::Op & __make_ ## Z3CVMOp ## _ ## OpName

#define Z3_REGISTER_OP(OpName)                                     \
  Z3UTIL_STR_CONCAT(Z3_REGISTER_VAR_DEF(OpName), __COUNTER__) = \
      ::z3::utils::Registry<::z3::cvm::Op>::Get()->__REGISTER_OR_GET__(#OpName)

}
}

#endif // Z3_CVM_OP_H
