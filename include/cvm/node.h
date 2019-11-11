#include <memory>
#include <vector>
#include <unordered_map>

#include <z3++.h>

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

// inline NodeEntry MakeNode(
//     const char* op_name,
//     std::string node_name,
//     std::vector<NodeEntry> inputs,
//     std::unordered_map<std::string, std::string> attrs =
//     std::unordered_map<std::string, std::string>()) {
//   NodePtr p = Node::Create();
//   p->attrs.op = cvm::Op::Get(op_name);
//   p->attrs.name = std::move(node_name);
//   p->attrs.dict = attrs;
//   if (p->attrs.op->attr_parser) {
//     p->attrs.op->attr_parser(&(p->attrs));
//   }
//   p->inputs = std::move(inputs);
//   return NodeEntry(p, 0, 0);
// }


}
}
