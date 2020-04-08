#include <iostream>
#include <fstream>
#include <unordered_map>
#include <ctime>
#include <cstdio>
#include <cstdlib>

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

void test_dense(){
  char st[15];
  for (int i = 1; i < 10; i++){
    for (int j = 1; j < 10; j++){
      for (int l = 1; l <= i; l++) {
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j}));
           auto b = Node::CreateVariable<TypeRef>("b", Shape({l, j}));
           sprintf(st, "%d", l);
           printf("%d %s ??\n",l, st);
           auto ret = Node::CreateOperator(
             "dense", "fully-connected", {a, b},
             unordered_map<string, string>{
             {"units", st},
             {"use_bias", "false"},
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
      }
    }
  }
}

void test_elemwise_add(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
           std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto b = Node::CreateVariable<TypeRef>("b", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
             "elemwise_add", "eadd", {a, b},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_relu(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
             "relu", "relu", {a},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_clip(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
             "clip", "clip", {a},
             unordered_map<string, string>{
                {"a_max", "10"},
                {"a_min", "-19"}
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_flatten(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
             "flatten", "flt", {a},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_repeat(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
             "repeat", "rpt", {a},
             unordered_map<string, string>{
                {"repeats", "2"}
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_upsampling(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
             "upsampling", "upsampling", {a},
             unordered_map<string, string>{
                {"scale", "2"}
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_concatenate(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto b  = Node::CreateVariable<TypeRef>("b", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
            "concatenate", "concat", {a, b},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_expand_dims(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
            "expand_dims", "expdim", {a},
             unordered_map<string, string>{
                {"axis", "2"},
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_squeeze(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
            "squeeze", "squeeze", {a},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_transpose(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
            "transpose", "trp", {a},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_tile(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
            "tile", "tl", {a},
             unordered_map<string, string>{
              {"reps", "(2,    2,   3,     )"},
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_slice(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto ret = Node::CreateOperator(
            "slice", "slice", {a},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_reshape(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           sprintf(st, "(%d, %d, %d, %d)", r, l, j, i);
           auto ret = Node::CreateOperator(
            "reshape", "rsp", {a},
             unordered_map<string, string>{
              {"shape", st},
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_cvm_clip(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           sprintf(st, "(%d, %d, %d, %d)", r, l, j, i);
           auto ret = Node::CreateOperator(
            "cvm_clip", "cvmclip", {a},
             unordered_map<string, string>{
                {"a_max", "10"},
                {"a_min", "-19"},
                {"precision", "2"},
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_slice_like(){
  char st[15];
  for (int i = 2; i < 3; i++){
    for (int j = 2; j < 100; j+=13){
      for (int l = 2; l <= 100; l+=17) {
        for (int r = 2; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto b = Node::CreateVariable<TypeRef>("b", Shape({i-1, j-1}));
           sprintf(st, "(%d, %d, %d, %d)", r, l, j, i);
           auto ret = Node::CreateOperator(
            "slice_like", "sli", {a, b},
             unordered_map<string, string>{
              {"axis", "(0, 1)"},
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_abs(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           sprintf(st, "(%d, %d, %d, %d)", r, l, j, i);
           auto ret = Node::CreateOperator(
            "abs", "abs", {a},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_cvm_right_shift(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           sprintf(st, "(%d, %d, %d, %d)", r, l, j, i);
           auto ret = Node::CreateOperator(
            "cvm_right_shift", "crs", {a},
             unordered_map<string, string>{
              {"precision", "2"},
              {"shift_bit", "2"},
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_cvm_left_shift(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           sprintf(st, "(%d, %d, %d, %d)", r, l, j, i);
           auto ret = Node::CreateOperator(
            "cvm_left_shift", "cls", {a},
             unordered_map<string, string>{
              {"precision", "2"},
              {"shift_bit", "2"},
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_broadcast_add(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto b = Node::CreateVariable<TypeRef>("b", Shape({i, j, l, r}));
           sprintf(st, "(%d, %d, %d, %d)", r, l, j, i);
           auto ret = Node::CreateOperator(
            "broadcast_add", "badd", {a, b},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_broadcast_sub(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto b = Node::CreateVariable<TypeRef>("b", Shape({i, j, l, r}));
           sprintf(st, "(%d, %d, %d, %d)", r, l, j, i);
           auto ret = Node::CreateOperator(
            "broadcast_sub", "bsub", {a, b},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_broadcast_mul(){
  char st[15];
  for (int i = 1; i < 2; i++){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, l, r}));
           auto b = Node::CreateVariable<TypeRef>("b", Shape({i, l, r}));
           sprintf(st, "(%d, %d, %d)", r, l, i);
           auto ret = Node::CreateOperator(
            "broadcast_mul", "bmul", {a, b},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
  }
}

void test_broadcast_div(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto b = Node::CreateVariable<TypeRef>("b", Shape({i, j, l, r}));
           sprintf(st, "(%d, %d, %d, %d)", r, l, j, i);
           auto ret = Node::CreateOperator(
            "broadcast_div", "bdiv", {a, b},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void test_broadcast_max(){
  char st[15];
  for (int i = 1; i < 2; i++){
    for (int j = 1; j < 100; j+=13){
      for (int l = 1; l <= 100; l+=17) {
        for (int r = 1; r <= 100; r+=23){
          std::cout << i << " " << j << " " << l << " " << r << std::endl;
           auto a = Node::CreateVariable<TypeRef>("a", Shape({i, j, l, r}));
           auto b = Node::CreateVariable<TypeRef>("b", Shape({i, j, l, r}));
           sprintf(st, "(%d, %d, %d, %d)", r, l, j, i);
           auto ret = Node::CreateOperator(
            "broadcast_max", "bmax", {a, b},
             unordered_map<string, string>{
           });
           for (auto &p : ret.node->provements_generator(true))
             z3_prover(p.cstr);
        }
      }
    }
  }
}

void big_test(std::string op_name){
  if (op_name == "dense"){
    test_dense(); 
  }
  if (op_name == "elemwise_add"){
    test_elemwise_add();
  }
  if (op_name == "relu"){
    test_relu();
  }
  if (op_name == "clip"){
    test_clip();
  }
  if (op_name == "flatten"){
    test_flatten();
  }
  if (op_name == "repeat"){
    test_repeat();
  }
  if (op_name == "upsampling"){
    test_upsampling();
  }
  if (op_name == "concatenate"){
    test_concatenate();
  }
  if (op_name == "expand_dims"){
    test_expand_dims();
  }
  if (op_name == "squeeze"){
    test_squeeze();
  }
  if (op_name == "transpose"){
    test_transpose();
  }
  if (op_name == "tile"){
    test_tile();
  }
  if (op_name == "slice"){
    test_slice();
  }
  if (op_name == "reshape"){
    test_reshape();
  }
  if (op_name == "slice_like"){
    test_slice_like();
  }
  if (op_name == "cvm_clip"){
    test_cvm_clip();
  }
  if (op_name == "abs"){
    test_abs();
  }
  if (op_name == "cvm_right_shift"){
    test_cvm_right_shift();
  }
  if (op_name == "cvm_left_shift"){
    test_cvm_left_shift();
  }
  if (op_name == "broadcast_add"){
    test_broadcast_add();
  }
  if (op_name == "broadcast_sub"){
    test_broadcast_sub();
  }
  if (op_name == "broadcast_mul"){
    test_broadcast_mul();
  }
  if (op_name == "broadcast_div"){
    test_broadcast_div();
  }
  if (op_name == "broadcast_max"){
    test_broadcast_max();
  }
}

int main() {
  // z3_expr_deterministic();
  // return 0;
  
  // generator_prove();
  // return 0;

  big_test("broadcast_max");
  return 0;
  int num_inputs = 3;
  auto a = Node::CreateVariable<TypeRef>("a", Shape({2, num_inputs}), 24);
  // auto b = Node::CreateVariable<Scalar>("b", 4);
  auto b = Node::CreateVariable<TypeRef>("b", Shape({2, num_inputs}));
  auto c = Node::CreateVariable<TypeRef>("c", Shape({2, 2, 2, 2}));
  auto d = Node::CreateVariable<TypeRef>("d", Shape({1, 3, 1}));
  auto e = Node::CreateVariable<TypeRef>("e", Shape({2, 2, 2}));
  auto f = Node::CreateVariable<TypeRef>("f", Shape({3, 4}));
  auto g = Node::CreateVariable<TypeRef>("g", Shape({2, 1}));
  auto h = Node::CreateVariable<TypeRef>("h", Shape({4, 2, 3, 4}));
  auto i = Node::CreateVariable<TypeRef>("i", Shape({2, 1, 1, 1}));
  auto ii = Node::CreateVariable<TypeRef>("ii", Shape({2, 1, 1, 1}));
  auto iii = Node::CreateVariable<TypeRef>("iii", Shape({2, }));

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
    //"broadcast_add", "badd", {b, g},
    // "broadcast_sub", "bsub", {b, g},
    //"broadcast_mul", "bmul", {b, g},
    //"broadcast_div", "bdiv", {b, g},
    //"broadcast_max", "bmax", {b, g},
    //"max_pool2d", "maxpool", {h},
    //"sum", "sum", {g},
    //"max", "max", {h},
    //"conv2d", "c2d", {i, ii, },
    "negative", "ngt", {a},




    unordered_map<string, string>{
    // {"units", "2"},
    {"use_bias", "false"},
    {"axis", "(1, )"},
    {"kernel_size", "(1, 1)"},
    {"channels", "2"},
    {"pool_size", "(1, 2)"},
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
