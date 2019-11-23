#include <memory>
#include <vector>
#include <unordered_map>

#include <z3++.h>

#include "cvm/node.h"

namespace z3 {
namespace cvm {

Node::~Node() {
  if (inputs.size() != 0) {
    // explicit deletion via DFS
    // this is used to avoid stackoverflow caused by chain of deletions
    std::vector<Node*> stack{this};
    std::vector<NodePtr> to_delete;
    while (!stack.empty()) {
      Node* n = stack.back();
      stack.pop_back();
      for (NodeEntry& e : n->inputs) {
        if (e.node.unique()) {
          stack.push_back(e.node.get());
          to_delete.emplace_back(std::move(e.node));
        } else {
          e.node.reset();
        }
      }
      n->inputs.clear();
    }
  }
}

NodeEntry Node::CreateVariable(
    const std::string &name,
    const Shape &shape) {
  NodePtr n = Node::Create();
  n->attrs.op = nullptr;
  n->attrs.name = name;
  n->data_.emplace_back(TypeRef::Make(name, shape));
  // append TypeRef's constraints
  n->csrt_ = n->data_[0]->constraints();
  n->asrt_ = n->data_[0]->assertions();
  // n->asrt_ = n->data_[0]->constraints() &&
    // n->data_[0]->assertions();
  return NodeEntry{n, 0, 0};
}


NodeEntry Node::CreateOperator(
    const char *op_name,
    const std::string &node_name,
    std::vector<NodeEntry> inputs,
    std::unordered_map<std::string, std::string> attrs) {
  NodePtr p = Node::Create();
  p->attrs.op = cvm::Op::Get(op_name);
  p->attrs.name = node_name;
  p->attrs.dict = attrs;
  p->inputs = std::move(inputs);

  VERIFY(p->inputs.size() == p->num_inputs())
    << "operator " << op_name << "(" << node_name << ")"
    << " inputs' size "
    << "not equals with " << p->num_inputs() << " vs. "
    << p->inputs.size();

  std::vector<TypePtr> data;
  for (auto &ne : p->inputs) {
    data.emplace_back(ne.operator->());
  }
  std::vector<TypePtr> outs;
  p->csrt_ = p->op()->forward_func(p->attrs, data, outs);
  
  for (size_t i = 0; i < outs.size(); ++i) {
    TypePtr &&tmp = TypeRef::Make(
        node_name+"_out"+std::to_string(i), outs[i]->shape);
    p->data_.emplace_back(tmp);
    p->csrt_ = p->csrt_ && tmp->assign(data[i]);
    p->asrt_ = p->asrt_ && outs[i]->constraints() &&
      outs[i]->assertions();
  }
  return NodeEntry(p, 0, 0);
}

z3_expr Node::constraints() const {
  z3_expr cstr(true);
  for (auto &ne : inputs) {
    cstr = cstr && ne.node->constraints();
  }
  cstr = cstr && this->csrt_;
  return cstr;
}

z3_expr Node::assertions() const {
  z3_expr asrt = this->asrt_;
  for (auto &ne : inputs) {
    asrt = asrt && ne.node->assertions();
  }
  return asrt;
}


}
}
