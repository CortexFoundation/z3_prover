#include <iostream>
#include <unordered_map>

#include "z3++.h"
#include "cvm/z3_types.h"
#include "cvm/op.h"
#include "cvm/node.h"

using namespace z3::cvm;
using namespace z3::type;
using namespace std;

void z3_prover(z3::expr cond) {
  z3::solver s(C);
  s.add(!cond);

  std::cout << "=== z3_prover ===\n" << s << std::endl;
  switch (s.check()) {
    case z3::unsat: 
      std::cout << "the model is deterministic." << std::endl;
      break;
    case z3::sat: {
      std::cout << "The model is undeterministic." << std::endl;
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
      std::cout << "The models is unknown" << std::endl;
      break;
    }

  }
}

int main() {
  auto a = Node::CreateVariable<Scalar>("a");
  auto b = Node::CreateVariable<Scalar>("b");

  auto c = Node::CreateOperator(
      "scalar_add", "add", {a, b},
      unordered_map<string, string>{
          // {"data_assign", "false"}
      });

  z3_expr cstr = c.node->constraints();
  z3_expr stmt = c->constraints();
  std::cout << cstr.val << "\n\n" << stmt.val << std::endl;

  z3::expr p1 = z3::implies(cstr.val, stmt.val);
  z3_prover(p1);
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
