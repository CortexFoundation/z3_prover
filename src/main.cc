#include <iostream>
#include <z3++.h>

#include "cvm/node.h"

using namespace z3;

int main() {
  std::cout << "z3_prover initialize" << std::endl;

  z3::context c;
  expr x = c.bool_const("x");
  expr y = c.bool_const("y");
  expr conjecture = (!(x && y)) == (!x || !y);
  
  solver s(c);
  // adding the negation of the conjecture as a constraint.
  s.add(!conjecture);
  std::cout << s << "\n";
  std::cout << s.to_smt2() << "\n";
  switch (s.check()) {
  case unsat:   std::cout << "de-Morgan is valid\n"; break;
  case sat:     std::cout << "de-Morgan is not valid\n"; break;
  case unknown: std::cout << "unknown\n"; break;
  }
}
