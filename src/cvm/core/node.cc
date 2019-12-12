#include <memory>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>

#include <z3++.h>

#include "cvm/node.h"

namespace z3 {
namespace cvm {

using namespace type;

NodeAssertions& NodeAssertions::add_input(
    TypePtr const& tp) {
  in_cstr = in_cstr && 
    tp->data_constraints() &&
    tp->prec_constraints();
  return *this;
}

NodeAssertions& NodeAssertions::add_input(
    TypePtr const& tp, size_t index) {
  in_cstr = in_cstr && 
    tp->data_constraints(index) &&
    tp->prec_constraints();
  return *this;
}

NodeAssertions& NodeAssertions::add_input(
    TypePtr const& tp, 
    std::vector<size_t> indexes) {
  for (size_t index : indexes) {
    in_cstr = in_cstr && tp->data_constraints(index);
  }
  in_cstr = in_cstr && tp->prec_constraints();
  return *this;
}

NodeAssertions& NodeAssertions::add_extra_constraint(
    z3_expr const& c) {
  in_cstr = in_cstr && c;
  return *this;
}

NodeAssertions& NodeAssertions::add_output(
    type::TypePtr const& tp) {
  in_cstr = in_cstr && 
    tp->assign_constraints() &&
    tp->prec_constraints();
  out_cstr = out_cstr &&
    tp->data_constraints() &&
    tp->op_constraints();
  return *this;
}

NodeAssertions& NodeAssertions::add_output(
    type::TypePtr const& tp, size_t index) {
  in_cstr = in_cstr &&
    tp->assign_constraints(index) &&
    tp->prec_constraints();
  out_cstr = out_cstr &&
    tp->data_constraints(index) &&
    tp->op_constraints(index);
  return *this;
}

z3_expr NodeAssertions::provement_generator() const {
  return type::implies(in_cstr, out_cstr);
}

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
  p->attrs.dict = std::move(attrs);
  p->inputs = std::move(inputs);

  // Set operator attributes default value
  if (p->op()->attr_def != nullptr)
    p->op()->attr_def(p->attrs);

  VERIFY_EQ(p->num_inputs(), p->inputs.size())
    << "operator " << op_name << "(" << node_name << ") "
    << "inputs' size invalid, Expected " << p->num_inputs()
    << " vs. " << p->inputs.size();
  p->forward();
  return NodeEntry(p, 0, 0);
}

void Node::forward() {
  std::vector<TypePtr> in_data;
  for (auto &ne : inputs) {
    in_data.emplace_back(ne.operator->());
  }
  VERIFY_NE(op(), nullptr)
    << "Node::forward() " << attrs.name
    << " variable has no operator";
  VERIFY_NE(op()->forward_func, nullptr)
    << "Node::forward() " << attrs.name
    << " variable has not registered foward_func";
  op()->forward_func(attrs, in_data, data_, nas_);
  VERIFY_EQ(data_.size(), num_outputs())
    << "operator " << op()->name << "(" << attrs.name << ") "
    << "outputs' size invalid, Expected " << num_outputs()
    << " vs. " << data_.size();
}

std::vector<z3_expr> 
Node::provements_generator(bool unique) {
  auto end = nas_.end();
  if (unique) end = std::unique(nas_.begin(), end);

  std::vector<z3_expr> proves;
  for (auto it = nas_.begin();it != end; ++it) {
    proves.push_back(it->provement_generator());
  }
  return proves;
}


}
}
