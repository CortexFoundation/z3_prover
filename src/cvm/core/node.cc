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

NodeAssertions& NodeAssertions::merge(NodeAssertions const& t) {
  in_cstr = in_cstr && t.in_cstr;
  out_cstr = out_cstr && t.out_cstr;
  unique_id = t.unique_id;
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
  std::cout << "shenqi " << p->num_inputs() << " " << p->inputs.size() << std::endl;
  VERIFY_EQ(p->num_inputs(), p->inputs.size())
    << "operator " << op_name << "(" << node_name << ") "
    << "inputs' size invalid, Expected " << p->num_inputs()
    << " vs. " << p->inputs.size();

  p->setup();
  return NodeEntry(p, 0, 0);
}

void Node::infer_shape() {
  VERIFY_NE(op()->infer_shape, nullptr)
    << "Node::infer_shape() " << op()->name
    << " operator has not registered FInferShape";

  std::vector<Shape> ishpes(inputs.size());
  for (size_t i = 0; i < inputs.size(); ++i) {
    ishpes[i] = inputs[i]->shape;
  }
  std::vector<Shape> oshpes(num_outputs());
  op()->infer_shape(attrs, ishpes, oshpes);
  VERIFY_EQ(oshpes.size(), num_outputs());
  nas_.resize(num_outputs(), {});
  for (size_t i = 0; i < oshpes.size(); ++i) {
    data_.emplace_back(TypeRef::Make(attrs.name, oshpes[i]));
    nas_[i].resize(oshpes[i].Size());
  }
}

void Node::infer_precision() {
  VERIFY_NE(op()->infer_precision, nullptr)
    << "Node::infer_precision() " << op()->name
    << " operator has not registered FInferPrecision";
  std::vector<z3_expr> iprecs(inputs.size(), z3_expr(0));
  std::vector<Shape> ishpes(inputs.size());
  for (size_t i = 0; i < inputs.size(); ++i) {
    iprecs[i] = inputs[i]->prec;
    ishpes[i] = inputs[i]->shape;
  }
  for (const auto& it : data_) {
    ishpes.push_back(it->shape);
  }
  std::vector<z3_expr> oprecs(num_outputs(), z3_expr(0));
  std::vector<NodeAssertions> nas(num_outputs());
  op()->infer_precision(attrs, ishpes, iprecs, oprecs, nas);
  VERIFY_EQ(oprecs.size(), num_outputs());
  VERIFY_EQ(data_.size(), num_outputs())
    << "Node must execute infer shape before "
    << "infer precision pass";
  for (size_t i = 0; i < oprecs.size(); ++i) {
    data_[i]->set_prec(oprecs[i]);
    for (size_t j = 0; j < data_[i]->Size(); ++j) {
      nas_[i][j].merge(nas[i]);
    }
  }
}

void Node::forward() {
  std::vector<TypePtr> in_data(inputs.size());
  for (size_t i = 0; i < in_data.size(); ++i) {
    in_data[i] = inputs[i].operator->();
  }
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
  std::vector<z3_expr> proves;
  std::unordered_set<size_t> uid_set;
  // Iterator over number of outputs.
  for (auto it = nas_.begin(); it != nas_.end(); ++it) {
    std::vector<NodeAssertions> out = *it;
    for (auto oit = out.begin();oit != out.end(); ++oit) {
      if (unique && // And not inserted successfully via exists
          !uid_set.insert(oit->get_uid()).second) 
        continue;
      proves.push_back(oit->provement_generator());
    }
  }
  return proves;
}


}
}
