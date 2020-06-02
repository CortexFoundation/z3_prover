#ifndef Z3_CVM_SYMBOLIC_H
#define Z3_CVM_SYMBOLIC_H

#include "node.h"

namespace z3 {
namespace cvm {

class Symbol {
 public:
  std::vector<NodeEntry> outputs;

  Symbol operator[](size_t index);

  Symbol GetChildren();

  static Symbol CreateVariable(const std::string &name);

};

Symbol operator+(const Symbol &lhs, const Symbol *&rhs);

}
}

#endif // Z3_CVM_SYMBOLIC_H
