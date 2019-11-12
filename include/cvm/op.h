#ifndef Z3_CVM_OP_H
#define Z3_CVM_OP_H

#include <memory>
#include <z3++.h>

#include "base.h"
#include "z3_types.h"
#include "registry.h"

namespace z3 {
namespace cvm {

struct NodeAttrs;
class Op;
template<typename ValueType>
class OpMap;

using namespace z3::type;
using Forward = std::function<
  std::vector<TypePtr>(const NodeAttrs& attrs,
                  std::vector<TypePtr>& inputs)>;

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

  inline Op& set_forward(const Forward& forward_func) {
    this->forward_ = forward_func;
    return *this;
  }

  inline std::vector<TypePtr>
  operator()(const NodeAttrs &attrs,
             std::vector<TypePtr> inputs) const;

  static const Op* Get(const std::string& op_name);

 private:
  friend class utils::Registry<Op>;

  uint32_t index_{0};
  Forward forward_{nullptr};
  Op();
};

#define Z3_REGISTER_VAR_DEF(OpName)                                   \
  static Z3UTIL_ATTRIBUTE_UNUSED ::z3::cvm::Op & __make_ ## Z3CVMOp ## _ ## OpName

#define Z3_REGISTER_OP(OpName)                                     \
  Z3UTIL_STR_CONCAT(Z3_REGISTER_VAR_DEF(OpName), __COUNTER__) = \
      ::z3::utils::Registry<::z3::cvm::Op>::Get()->__REGISTER_OR_GET__(#OpName)

std::vector<TypePtr>
Op::operator()(const NodeAttrs &attrs,
               std::vector<TypePtr> inputs) const {
  if (this->forward_ == nullptr) {
    throw std::runtime_error(
        "Operator " + this->name +
        " forward function not registered");
  }
  return this->forward_(attrs, inputs);
}

}
}

#endif // Z3_CVM_OP_H