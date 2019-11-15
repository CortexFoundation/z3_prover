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

  std::vector<TypePtr> data;
  for (auto &ne : p->inputs) {
    data.emplace_back(ne.operator->());
  }
  // z3_expr cstr = p->op()->constraints(p->attrs, data);
  std::vector<TypePtr> outs;
  z3_expr cstr = p->op()->forward_func(p->attrs, data, outs);
  
  if ((attrs.count("data_assign") == 0) ||
      (attrs.at("data_assign") == "true")) {
    for (size_t i = 0; i < outs.size(); ++i) {
      TypePtr &&tmp = outs[i]->copy_placeholder(
          node_name + "_assign" + std::to_string(i));
      cstr = cstr && tmp->assign(data[i]);
      p->data_.emplace_back(tmp);
    }
  } else {
    p->data_ = data;
  }
  p->constraints_ = cstr;
  return NodeEntry(p, 0, 0);
}

z3_expr Node::constraints() const {
  z3_expr cstr = this->constraints_; // operator's constraint
  if (inputs.size() > 0) {
    z3_expr t = inputs[0].node->constraints();
    for (size_t i = 1; i < inputs.size(); ++i) {
      t = t && inputs[i].node->constraints();
    }
    cstr = t && cstr;
  }
  return cstr;
}


}
}
