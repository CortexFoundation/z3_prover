#include <memory>
#include <vector>
#include <unordered_map>

#include <z3++.h>

#include "cvm/node.h"

namespace z3 {
namespace cvm {

using namespace type;

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
  std::vector<TypePtr> outs;

  VERIFY_EQ(data.size(), p->num_inputs())
    << "operator " << op_name << "(" << node_name << ") "
    << "inputs' size "
    << "not equals with " << p->num_inputs() << " vs. "
    << p->inputs.size();
  p->csrt_ = p->op()->forward_func(p->attrs, data, outs);
  VERIFY_EQ(outs.size(), p->num_outputs())
    << "operator " << op_name << "(" << node_name << ") "
    << "outputs' size "
    << "not equal with " << p->num_outputs() << " vs. "
    << outs.size();
  
  for (size_t i = 0; i < outs.size(); ++i) {
    TypePtr &&tmp = outs[i]->copy(
        node_name + "_out" + std::to_string(i));
    // TypePtr &&tmp = TypeRef::Make(
        // node_name+"_out"+std::to_string(i), outs[i]->shape);
    p->data_.emplace_back(tmp);
    // p->csrt_ = p->csrt_ && tmp->assign(outs[i]);
    p->asrt_ = p->asrt_ && tmp->data_constraints() &&
      tmp->op_constraints();
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
