#include <iostream>
#include <unordered_map>
#include <ctime>

#include "cvm/z3_types.h"
#include "cvm/op.h"
#include "cvm/node.h"

using namespace z3::cvm;
using namespace z3::type;
using namespace std;

void z3_prover(z3_cstr cstr, ostream &os=cout) {
  z3::solver s(C);
#if SIMPLIFY_LEVEL <= 5
  s.add(!cstr);
#else
  s.add((!cstr).simplify());
#endif

  os << "===== z3_prover =====\n" << s << std::endl;
  clock_t start = clock();
  switch (s.check()) {
    case z3::unsat: 
      os << "the model is deterministic." << std::endl;
      break;
    case z3::sat: {
      os << "The model is undeterministic." << std::endl;
      z3::model m = s.get_model();
      for (unsigned i = 0; i < m.size(); i++) {
        z3::func_decl v = m[i];
        // this problem contains only constants
        // assert(v.arity() == 0);
        std::cout << v.name() << " = ";
        if (v.arity() == 0)
          std::cout << m.get_const_interp(v);
        else
          std::cout << m.get_func_interp(v);
        std::cout << "\n";
      }
      break;
    }
    case z3::unknown: {
      os << "The models is unknown" << std::endl;
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

int main() {
  // z3_expr_deterministic();
  // return 0;
  //
  // std::cout << DEBUG_STR(F_Z3_EXPR_DECL(operator+, 3)) << std::endl;
  // return 0;

  auto a = Node::CreateVariable<TypeRef>("a", Shape(), 24);
  auto b = Node::CreateVariable<Scalar>("b", 4);
  // auto b = Node::CreateVariable<TypeRef>("b", Shape());

  auto c = Node::CreateOperator(
      "elemwise_add", "add", {a, b},
      unordered_map<string, string>{
          // {"data_assign", "false"}
      });

  z3_expr cstr = c.node->constraints();
  z3_expr asrt = c.node->assertions();

  z3_prover(implies(cstr, asrt).cstr);
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
