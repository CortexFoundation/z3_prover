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
class Symbol;

using NodePtr = std::shared_ptr<Node>;

struct NodeEntry {
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

  NodePtr node;
  uint32_t index;
  uint32_t version;
};

struct NodeEntryHash {
  size_t operator()(const NodeEntry& e) const {
    return std::hash<Node*>()(e.node.get()) ^
          (std::hash<size_t>()(e.index) << 1 >> 1) ^
          (std::hash<size_t>()(e.version) << 1);
  }
};

struct NodeEntryEqual {
  size_t operator()(const NodeEntry& a, const NodeEntry& b) const {
    return (a.node.get() == b.node.get()) &&
           (a.index == b.index) &&
           (a.version == b.version);
  }
};

template<typename ValueType>
using NodeEntryMap = std::unordered_map<NodeEntry, ValueType, NodeEntryHash, NodeEntryEqual>;

struct NodeAttrs {
  const Op *op{nullptr};
  std::string name;
  std::unordered_map<std::string, std::string> dict;
};

class Node {
 public:
  Node() = default;
  Node(const Op* op, const std::string name) {
    this->attrs.op = op;
  }

  NodeAttrs attrs;
  std::vector<NodeEntry> inputs;

  ~Node();

  inline const Op* op() const;

  inline bool is_variable() const;

  inline uint32_t num_inputs() const;
  inline uint32_t num_outputs() const;

  template<class ...Args>
  static NodePtr Create(Args&&... args) {
    return std::make_shared<Node>(std::forward<Args>(args)...);
  }
};

inline NodeEntry MakeNode(
    const char* op_name,
    std::string node_name,
    std::vector<NodeEntry> inputs,
    std::unordered_map<std::string, std::string> attrs =
    std::unordered_map<std::string, std::string>()) {
  NodePtr p = Node::Create();
  p->attrs.op = cvm::Op::Get(op_name);
  p->attrs.name = std::move(node_name);
  p->attrs.dict = attrs;
  p->inputs = std::move(inputs);
  return NodeEntry(p, 0, 0);
}

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


}
}

#endif // Z3_CVM_NODE_H