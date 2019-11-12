#include <iostream>

#include "z3++.h"
#include "cvm/z3_types.h"
#include "cvm/op.h"
#include "cvm/node.h"

using namespace z3;

int main() {
  std::cout << "z3_prover initialize" << std::endl;

  type::TypePtr a = type::Scalar::Make("a");
  type::TypePtr b = type::Scalar::Make("b");
  std::cout << a->constraints() << "\n"
    << a->deterministic() << std::endl;

  const cvm::Op *op = cvm::Op::Get("scalar_add");
  cvm::NodeAttrs attrs;
  auto &&c = op->operator()(attrs, {a, b});
  std::cout << "\n"
    << c[0]->constraints() << "\n"
    << c[0]->deterministic() << std::endl;
  return 0;

}
