#include "cvm/z3_types.h"
#include "common.h"
#include <numeric>
#include <algorithm>
namespace z3 {
namespace cvm {

using namespace z3::type;

std::vector<z3_expr> _sum_prove() {
  return {};
}

static void SumAttrDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "axis", "()");
  ATTR_DEFAULT(attrs, "keepdims", "false");
  ATTR_DEFAULT(attrs, "exclude", "false");
}

inline std::vector<int64_t> GetRealAxis(Shape& axis, bool exclude, int x_ndim){
  for(size_t i = 0; i < axis.size(); i++){
    if(axis[i] < 0) axis[i] += x_ndim;
  }
  std::vector<int64_t> raxis;
  if(!exclude){
    for(size_t i = 0; i < axis.size(); i++){
      raxis.push_back(axis[i]);
    }
  }else{
    raxis.resize(x_ndim - axis.size());
    for(int i = 0, k = 0; i < x_ndim; i++){
      bool flag = false;
      for(size_t j = 0; j < axis.size(); j++){
        if(axis[j] == i) {
          flag = true;
          break;
        }
      }
      if(!flag){
        raxis[k++] = i;
      }
    }
  }
  return raxis;
}
typedef std::function<void(z3_expr&, z3_expr)> reduce_func;
static void SumForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  TypePtr const& x = inputs.at(0);
  TypePtr& y = outputs.at(0);
  std::string const st_axis = attrs.dict.at("axis");
  Shape axis = Shape::from_string(st_axis);
  std::string st_keepdims = attrs.dict.at("keepdims");
  bool keepdims;
  std::istringstream(st_keepdims) >> std::boolalpha >> keepdims;
  std::string st_exclude = attrs.dict.at("exclude");
  bool exclude;
  std::istringstream(st_exclude) >> std::boolalpha >> exclude;
  

  reduce_func f = [](z3_expr& tmp, z3_expr value)->void {
    tmp = tmp + value;
  };


  std::vector<int64_t> realAxis = GetRealAxis(axis, exclude, x->ndim());

  if(exclude && realAxis.size() == 0){
    std::cout << "test1" << std::endl; 
    for (size_t i = 0; i < y->Size(); ++i) {
       y->set_data(i, x->at(i));
       nas[0].at(i)
         .add_input(x, i)
         .add_output(y, i);
     }
  } else if (realAxis.size() == 0) {
    std::cout << "test2" << std::endl;
    z3_expr tmp = 0;
    for(uint64_t i = 0; i < x->Size(); i++){
      f(tmp, x->at(i));
      nas[0].at(0).add_input(x, i);
    }
    nas[0].at(0).add_output(y, 0);
    y->set_data(0, tmp);
  } else {
    std::cout << "test3" << std::endl;
    std::vector<bool> flag(x->ndim(), false);
    for(uint32_t i = 0; i < realAxis.size(); i++){
      int32_t val = realAxis[i];
      flag[val] = true;
    }
    std::sort(realAxis.begin(), realAxis.end());

    uint64_t axis_size = 1;
    for(uint32_t i = 0; i < realAxis.size(); i++){
      axis_size *= x->shape[realAxis[i]];
    }
    std::vector<uint64_t> every_xdim_size(x->ndim(), 1);
    for(int i = x->ndim()-2; i >= 0; i--){
      every_xdim_size[i] = x->shape[i+1] * every_xdim_size[i+1];
    }
    // foreach yshp, remove the dimension equals 1
    // special case: input shape is (1,), considered.
    int32_t yndim = y->ndim();
    std::vector<int64_t> yshape(y->ndim(), 1);
    for(int i = 0, j = 0; i < y->ndim(); i++){
      if(y->shape[i] == 1) {
        yndim -= 1;
      }else{
        yshape[j++] = y->shape[i];
      }
    }
    /* For example:
     * xshp : (n1, n2, n3, n4) -> yshp(n1, n4)
     * find x indexes reduce to yi with two steps:
     *  1. x start index, xvar(n1, 0, 0, n4)
     *  2. foreach reduce axis dimension(n2, n3), 
     *      get x possible indexes and add value to result.
     **/
    for(uint64_t i = 0; i < y->Size(); i++){
      uint64_t in_i = 0, o_i = i;
      for(int j = yndim-1, xj = x->ndim()-1; j>=0; j--){
        uint64_t col = o_i % yshape[j];
        o_i /= yshape[j];
        while(xj >= 0 && flag[xj--]);
        in_i += col * every_xdim_size[xj+1];
      }
      auto tmp = x->at(in_i);
      nas[0].at(i).add_input(x, in_i);
      for(uint64_t xi = 1; xi < axis_size; xi++){
        uint64_t o_i = xi, tmp_in_i = 0;
        for(int j = realAxis.size() - 1; j>=0; j--){
          uint64_t col = o_i % x->shape[realAxis[j]];
          o_i /= x->shape[realAxis[j]];
          tmp_in_i += col * every_xdim_size[realAxis[j]];
        }
        f(tmp, x->at(in_i+tmp_in_i));
        nas[0].at(i).add_input(x, in_i+tmp_in_i);
      }
      y->set_data(i, tmp);
      nas[0].at(i).add_output(y, i);
    }
  }
  
}

inline Shape GetReduceAxes(const uint32_t indim,
                            const Shape& axis,
                            bool exclude) {
  if (axis.size() == 0) {
    Shape r_axes(indim);
    std::iota(r_axes.begin(), r_axes.end(), 0);
    return r_axes;
  }

  Shape in_axis = axis;
  for (auto& i : in_axis) {
    i = i < 0 ? i + indim : i;
    VERIFY(0 <= i && i < indim);
  }
  std::sort(in_axis.begin(), in_axis.end());
  for(size_t i = 0; i < in_axis.size()-1; i++){
    VERIFY(in_axis[i] != in_axis[i+1]);
  }
  if (!exclude) return in_axis;
  Shape r_axis(indim - in_axis.size());
  for (unsigned i = 0, j = 0, k = 0; i < indim; ++i) {
    if (j < in_axis.size() && i == in_axis[j]) {
        ++j;
        continue;
    }
    r_axis[k++] = i;
  }
  return r_axis;
}

static void SumInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 1U);
  VERIFY(ishpes.at(0).size() != 0);
  const auto& ishape = ishpes.at(0); 
  uint32_t indim = ishape.size();
  
  std::string const st_axis = attrs.dict.at("axis");
  Shape axis = Shape::from_string(st_axis);
  std::string st_keepdims = attrs.dict.at("keepdims");
  bool keepdims;
  std::istringstream(st_keepdims) >> std::boolalpha >> keepdims;
  std::string st_exclude = attrs.dict.at("exclude");
  bool exclude;
  std::istringstream(st_exclude) >> std::boolalpha >> exclude;
  int ndims = ishpes.at(0).size();
  Shape r_axes = GetReduceAxes(indim, axis, exclude);
  if (!r_axes.size()){ 
    oshpes.at(0) = ishape;
    return;
  }
  if (r_axes.size() == indim){
    oshpes.at(0) = Shape(keepdims ? indim : 1);
    return; 
  }
  VERIFY(r_axes.size() < indim);
  if (keepdims) {
    Shape oshape(ishape);
    for (unsigned i = 0, j = 0; i < indim; ++i) {
      if (j >= r_axes.size() || i != r_axes[j]) continue;
      oshape[i] = 1;
      ++j;
    }
    oshpes.at(0) = oshape;
    return;
  }
  
  Shape oshape(indim - r_axes.size());
  for (unsigned i = 0, j = 0, k = 0; i < indim; ++i) {
    if (j < r_axes.size() && i == r_axes[j]) {
      ++j;
      continue;
    }
    oshape[k++] = ishape[i];
  }
  oshpes.at(0) = oshape;
}

static void SumInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  const Shape& ishp = ishpes.at(0);
  const Shape& oshp = ishpes.at(1);
  int64_t suml = ishp.Size() / oshp.Size();
  auto oprec = iprecs.at(0);
  oprec = oprec + GetBit(suml);
  oprecs[0] = oprec;
}

Z3_REGISTER_OP(sum)
  .set_num_inputs(1)
  .set_num_outputs(1)
  .set_attr_default(SumAttrDefault)
  .set_forward(SumForward)
  .set_infer_shape(SumInferShape)
  .set_infer_precision(SumInferPrecision)
  .set_generator(_sum_prove);

}
}
