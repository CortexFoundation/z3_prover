#include <iostream>
#include <fstream>
#include <unordered_map>
#include <ctime>

#include "cvm/z3_types.h"
#include "cvm/op.h"
#include "cvm/node.h"

using namespace z3::cvm;
using namespace z3::type;
using namespace std;

#define DOUBLE_LOG(msg) \
  os << msg << std::endl; \
  if (&os != &std::cout) \
    std::cout << msg << std::endl;

void z3_prover(z3_cstr cstr, ostream &os=cout) {
  z3::solver s(C);
#if SIMPLIFY_LEVEL <= 6
  s.add(!cstr);
#else
  s.add((!cstr).simplify());
#endif

  os << "===== Z3_PROVER =====\n" 
    << s
    << "===== END =====\n" << std::endl;
  clock_t start = clock();
  switch (s.check()) {
    case z3::unsat: 
      DOUBLE_LOG("The model is deterministic");
      break;
    case z3::sat: {
      DOUBLE_LOG("The model is undeterministic");
      z3::model m = s.get_model();
      for (unsigned i = 0; i < m.size(); i++) {
        z3::func_decl v = m[i];
        // this problem contains only constants
        // assert(v.arity() == 0);
        os << v.name() << " = ";
        if (v.arity() == 0)
          os << m.get_const_interp(v);
        else
          os << m.get_func_interp(v);
        os << "\n";
      }
      break;
    }
    case z3::unknown: {
      DOUBLE_LOG("The model is unprovable");
      break;
    }
  }

  clock_t interval = clock() - start;
  os << "Time: " << double(interval) / CLOCKS_PER_SEC
    << "s" << std::endl;
}

void z3_expr_deterministic() {
  z3_expr a("a"), b("b");
  z3_expr cstr = a.deterministic() && b.deterministic();
  z3_expr res(true);

  res = a + b;
  z3_prover(implies(cstr, res).cstr);
  res = a - b;
  z3_prover(implies(cstr, res).cstr);
  res = a * b;
  z3_prover(implies(cstr, res).cstr);
  res = a / b;
  z3_prover(implies(cstr, res).cstr);
  res = op_max(a, b);
  z3_prover(implies(cstr, res).cstr);

  res = - a;
  z3_prover(implies(a.deterministic(), res).cstr);

  // shift left operator must bewteen [1, 31]
  // res = op_1_shift_left(a);
  // z3_prover(implies(a.deterministic(), res).cstr);
}

void generator_prove() {
  // std::vector<std::string> op_names = Op::ListAllNames();
  // ofstream os("/tmp/verify.log");
  std::vector<std::string> op_names = { "elemwise_mul" };
  ostream &os = std::cout;
  for (string name : op_names) {
    auto oppg = Op::Get(name)->provements_generator;
    if (oppg != nullptr) {
      os << "\n\nVerification Operator: "
        << name << "\n" << std::endl;

      for (auto &p : oppg()) z3_prover(p.cstr, os);
    }
    
  }
}

int main() {
  // z3_expr_deterministic();
  // return 0;
  
  generator_prove();
  return 0;

  int num_inputs = 64;
  auto a = Node::CreateVariable<TypeRef>("a", Shape({16, num_inputs}), 24);
  // auto b = Node::CreateVariable<Scalar>("b", 4);
  auto b = Node::CreateVariable<TypeRef>("b", Shape({2, num_inputs}));

  auto c = Node::CreateOperator(
      "dense", "add", {a, b},
      unordered_map<string, string>{
        {"units", "2"},
        {"use_bias", "false"},
      });
  for (auto &p : c.node->provements_generator(true))
    z3_prover(p.cstr);

  return 0;


  // ktype::TypePtr a = type::Scalar::Make("a");
  // ktype::TypePtr b = type::Scalar::Make("b");
  // kstd::cout << a->constraints() << "\n"
  // k  << a->deterministic() << std::endl;

  // kconst cvm::Op *op = cvm::Op::Get("scalar_add");
  // kcvm::NodeAttrs attrs;
  // kauto &&c = op->operator()(attrs, {a, b});
  // kstd::cout << "\n"
  // k  << c[0]->constraints() << "\n"
  // k  << c[0]->deterministic() << std::endl;
  return 0;

}
