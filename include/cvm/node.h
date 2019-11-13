#ifndef Z3_CVM_NODE_H
#define Z3_CVM_NODE_H

#include <memory>
#include <vector>
#include <unordered_map>

#include "z3++.h"
#include "op.h"

namespace z3 {
namespace cvm {

class Node;
class NodeEntry;
using NodePtr = std::shared_ptr<Node>;

struct NodeAttrs {
  const Op *op{nullptr};
  std::string name;
  std::unordered_map<std::string, std::string> dict;
};

class Node {
 public:
  NodeAttrs attrs;
  std::vector<NodeEntry> inputs;

  ~Node();

  inline const Op* op() const;

  inline bool is_variable() const;

  inline uint32_t num_inputs() const;
  inline uint32_t num_outputs() const;

  expr constraints() const;
  // expr deterministic() const;

  template<typename ValueType>
  static NodeEntry CreateVariable(const std::string &name);

  static NodeEntry CreateOperator(
      const char *op_name,
      const std::string &name,
      std::vector<NodeEntry> inputs,
      std::unordered_map<std::string, std::string> attrs = 
      std::unordered_map<std::string, std::string>());

 private:
  friend class NodeEntry;
  std::vector<type::TypePtr> data_;
  expr constraints_{C};
  expr deterministic_{C};

  Node() = default;
  static NodePtr Create() {
    return std::make_shared<Node>(Node());
  }

};

class NodeEntry {
 public:
  NodeEntry(NodePtr node, uint32_t index, uint32_t version):
    node(std::move(node)),
    index(index),
    version(version)
  {}

  NodeEntry():
    node(),
    index(),
    version()
  {}

  inline const TypePtr operator->() {
    return this->node->data_[index];
  }

  NodePtr node;
  uint32_t index;
  uint32_t version;
};

inline const Op* Node::op() const {
  return this->attrs.op;
}

inline bool Node::is_variable() const {
  return this->op() == nullptr;
}

inline uint32_t Node::num_outputs() const {
  if (is_variable()) return 1;
  if (this->op()->get_num_outputs == nullptr) {
    return this->op()->num_outputs;
  } else {
    return this->op()->get_num_outputs(this->attrs);
  }
}

inline uint32_t Node::num_inputs() const {
  if (is_variable()) return 1;
  if (this->op()->get_num_inputs == nullptr) {
    return this->op()->num_inputs;
  } else {
    return this->op()->get_num_inputs(this->attrs);
  }
}

template <typename ValueType>
NodeEntry Node::CreateVariable(const std::string &name) {
  NodePtr n = Node::Create();
  n->attrs.op = nullptr;
  n->attrs.name = name;
  n->data_.emplace_back(ValueType::Make(name));
  // append TypeRef's constraints
  n->constraints_ = n->data_[0]->constraints();
  n->deterministic_ = n->data_[0]->deterministic();
  return NodeEntry{n, 0, 0};
}


}
}

#endif // Z3_CVM_NODE_H
