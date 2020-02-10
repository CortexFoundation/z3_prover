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
  std::vector<std::string> op_names = { "elemwise_add" };
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
  
  // generator_prove();
  // return 0;

  int num_inputs = 3;
  auto a = Node::CreateVariable<TypeRef>("a", Shape({2, num_inputs}), 24);
  // auto b = Node::CreateVariable<Scalar>("b", 4);
  auto b = Node::CreateVariable<TypeRef>("b", Shape({2, num_inputs}));
  auto c = Node::CreateVariable<TypeRef>("c", Shape({2, 2, 2, 2}));
  auto d = Node::CreateVariable<TypeRef>("d", Shape({1, 3, 1}));
  auto e = Node::CreateVariable<TypeRef>("e", Shape({2, 2, 2}));
  auto f = Node::CreateVariable<TypeRef>("f", Shape({3, 4}));
  auto g = Node::CreateVariable<TypeRef>("g", Shape({2, 1}));

  auto ret = Node::CreateOperator(
    // "dense", "fully-connected", {a, b},
    // "elemwise_add", "add", {a, b},
    // "relu", "add", {b},
    // "clip", "clip", {a},
    // "flatten", "flt", {a},
    // "repeat", "rpt", {a},
    //"upsampling", "upsampling", {c},
    //"concatenate", "concat", {a, b},
    //"expand_dims", "expdim", {c},
    //"squeeze", "squeeze", {d},
    //"transpose", "trp", {e},
    // "tile", "tl", {a},
    //"slice", "slice", {f},
    //"reshape", "rsp", {f},
    //"slice_like", "sli", {f, b},
    //"cvm_clip", "cvmclie", {a},
    //"abs", "abs", {a},
    //"cvm_precision", "cvmpre", {a},
    //"cvm_right_shift", "crs", {a},
    //"cvm_left_shift", "cls", {a},
    "broadcast_add", "badd", {b, g},





    unordered_map<string, string>{
    // {"units", "2"},
    // {"use_bias", "false"},
    //{"axis", "1"},
    {"precision", "2"},
    {"shift_bit", "2"},
    {"begin", "(0, 1)"},
    {"shape", "(2, 2, 3)"},
    {"end", "(2,4)"},
    //{"axis", "(0, 2)"},
    //{"axes", "(1, 0, 2)"},
    {"repeats", "2"},
    {"reps", "(2,    2,   3,     )"},
    {"a_max", "10"},
    {"a_min", "-19"},
    {"scale", "2"},
  });
  for (auto &p : ret.node->provements_generator(true))
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
