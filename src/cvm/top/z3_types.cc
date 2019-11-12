#include "z3++.h"
#include "cvm/z3_types.h"

namespace z3 {
namespace type {

context& Z3Context() {
  static context inst;
  return inst;
}

expr InClosedInterval(expr x, expr start, expr end) {
  return (start <= x) && (x <= end);
}
expr InClosedInterval(expr x, int start, int end) {
  return InClosedInterval(x, C.int_val(start), C.int_val(end));
}
expr BitRange(expr prec) {
  return (z3::pw(2, (prec - 1)) - 1);
}

}
}
