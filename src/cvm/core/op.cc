#include <vector>
#include <atomic>
#include <mutex>
#include <unordered_set>
#include <unordered_map>

#include "cvm/op.h"

namespace z3 {
namespace utils {
  Z3UTIL_REGISTRY_ENABLE(cvm::Op);
}
}

namespace z3 {
namespace cvm {

// single manager of operator information.
struct OpManager {
  std::recursive_mutex mutex;
  std::atomic<int> op_counter{0};
  std::unordered_map<std::string, std::vector<std::function<void(Op*)>  > > tmap;
  std::vector<std::unordered_set<std::string> > op_group;

  static OpManager* Global() {
    static OpManager inst;
    return &inst;
  }
};

Op::Op() {
  OpManager* mgr = OpManager::Global();
  index_ = mgr->op_counter;
}

const Op* Op::Get(const std::string &name) {
  const Op* op = utils::Registry<Op>::Find(name);
  if (op == nullptr) {
    throw std::runtime_error("Operator " + name + " is not registered.");
  }
  return op;
}

// const Op* Op::Get(const std::string& name) {
//   const Op* op = 
// }


}
}
