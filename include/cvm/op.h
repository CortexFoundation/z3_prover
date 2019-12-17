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
class NodeAssertions;

using func_pg = std::function<
  std::vector<type::z3_expr>()>;
using func_forward = std::function<
  void(NodeAttrs const& attrs,
      std::vector<type::TypePtr>& inputs,
      std::vector<type::TypePtr>& outputs,
      std::vector<NodeAssertions> &nas)>;

class Op {
 public:
  std::string name;

  uint32_t num_inputs = 1;
  uint32_t num_outputs = 1;

  using FNumOutputs = 
  std::function<uint32_t(const NodeAttrs& attrs)>;
  FNumOutputs get_num_outputs = nullptr;
  using FNumInputs = 
  std::function<uint32_t(const NodeAttrs& attrs)>;
  FNumInputs get_num_inputs = nullptr;

  inline Op& set_num_inputs(uint32_t n) {
    this->num_inputs = n;
    return *this;
  }
  inline Op& set_num_inputs(FNumInputs const& fn) {
    this->get_num_inputs = fn;
    return *this;
  }

  inline Op& set_num_outputs(uint32_t n) {
    this->num_outputs = n;
    return *this;
  }
  inline Op& set_num_outputs(FNumOutputs const& fn) {
    this->get_num_outputs = fn;
    return *this;
  }

  std::function<void(NodeAttrs& attrs)> attr_def = nullptr;
  inline Op& set_attr_default(
      std::function<void(NodeAttrs& attrs)> const& p) {
    this->attr_def = p;
    return *this;
  }

  using FInferShape = 
    std::function<void(NodeAttrs const& attrs,
      std::vector<type::Shape> &ishpes,
      std::vector<type::Shape> &oshpes)>;
  FInferShape infer_shape = nullptr;
  inline Op& set_infer_shape(FInferShape const& p) {
    this->infer_shape = p;
    return *this;
  }

  using FInferPrecision =
    std::function<std::vector<NodeAssertions>(
        NodeAttrs const& attrs,
        std::vector<type::Shape> &ishpes,
        std::vector<type::z3_expr> &iprecs,
        std::vector<type::z3_expr> &oprecs)>;
  FInferPrecision infer_precision = nullptr;
  inline Op& set_infer_precision(FInferPrecision const& fn) {
    this->infer_precision = fn;
    return *this;
  }

  func_forward forward_func = nullptr;
  inline Op& set_forward(
      func_forward const& forward_func) {
    this->forward_func = forward_func;
    return *this;
  }

  func_pg provements_generator = nullptr;
  inline Op& set_generator(func_pg const& func) {
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

#define ATTR_DEFAULT(attrs, key, value) \
  if (attrs.dict.count(key) == 0) attrs.dict[key] = value;
#define ATTR_DECL(attrs, key) \
  VERIFY_NE(attrs.dict.count(key), 0) \
    << "operator " << attrs.op->name \
    << "(" << attrs.name << ")" \
    << " forget to set attribute: " << key;

}
}

#endif // Z3_CVM_OP_H
