#ifndef Z3_CVM_NODE_H
#define Z3_CVM_NODE_H

#include <memory>
#include <vector>
#include <unordered_map>
#include <unordered_set>

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

class NodeAssertions {
 public:
  NodeAssertions() = default;
  NodeAssertions(size_t uid)
    : unique_id(uid) {}

  NodeAssertions& set_unique_id(size_t uid) {
    unique_id = uid;
    return *this;
  }

  NodeAssertions& add_input(type::TypePtr const&);
  NodeAssertions& add_input(type::TypePtr const&, size_t);
  NodeAssertions& add_input( type::TypePtr const&, std::vector<size_t>);
  NodeAssertions& add_extra_constraint(type::z3_expr const&);

  NodeAssertions& add_output(type::TypePtr const&);
  NodeAssertions& add_output(type::TypePtr const&, size_t);

  type::z3_expr provement_generator() const;
  inline bool operator==(NodeAssertions const& t) const {
    return unique_id == t.unique_id;
  }

 private:
  type::z3_expr in_cstr{true};
  type::z3_expr out_cstr{true};
  size_t unique_id{0};
};

class Node {
 public:
  NodeAttrs attrs;
  std::vector<NodeEntry> inputs;

  Node() = default;
  ~Node();
  static NodePtr Create() {
    return std::make_shared<Node>(Node());
  }

  inline const Op* op() const;

  inline bool is_variable() const;

  inline uint32_t num_inputs() const;
  inline uint32_t num_outputs() const;

  void forward();
  std::vector<type::z3_expr> provements_generator(
      bool unique = true);

  template<typename ValueType = type::TypeRef, typename ...Args>
  static NodeEntry CreateVariable(
      const std::string &node_name, 
      Args&& ...args);

  static NodeEntry CreateOperator(
      const char *op_name,
      const std::string &name,
      std::vector<NodeEntry> inputs,
      std::unordered_map<std::string, std::string> attrs = 
      std::unordered_map<std::string, std::string>());

 private:
  friend class NodeEntry;
  std::vector<type::TypePtr> data_;
  std::vector<NodeAssertions> nas_;
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

  inline const type::TypePtr operator->() {
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

template<typename ValueType, typename ...Args>
NodeEntry Node::CreateVariable(
    const std::string &node_name,
    Args&& ...args) {
  NodePtr n = Node::Create();
  n->attrs.op = nullptr;
  n->attrs.name = node_name;
  n->data_.emplace_back(ValueType::Make(
        node_name,
        std::forward<Args>(args)...));
  for (size_t i = 0; i < n->data_[0]->Size(); ++i) {
    n->nas_.emplace_back(
        NodeAssertions()
        .add_input(n->data_[0], i)
        .add_output(n->data_[0], i));
  }
  return NodeEntry{n, 0, 0};
}

}
}

#endif // Z3_CVM_NODE_H
