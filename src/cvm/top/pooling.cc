#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

BIN_OP_FUNC(op_max, a, b) {
  return type::op_max(a, b);
};
BIN_PREC_FUNC(prec_max, a, b) {
  return type::op_max(a, b);
};

static void MaxPool2dAttrDefault(NodeAttrs& attrs) {
  ATTR_DECL(attrs, "pool_size");
  ATTR_DEFAULT(attrs, "strides", "(1, 1)");
  ATTR_DEFAULT(attrs, "padding", "(0, 0)");
  ATTR_DEFAULT(attrs, "layout", "NCHW");
  ATTR_DEFAULT(attrs, "ceil_mode", "false");
}

inline bool shape_assign(Shape *y, const Shape& x) {
  if (y->size() == 0) {
    *y = x;
    return true;
  } else if (y->size() != x.size()) {
    return x.size() == 0;
  } else {
    for (size_t i = 0; i < y->size(); ++i) {
      if ((*y)[i] == 0) {
        (*y)[i] = x[i];
      } else if ((*y)[i] != x[i] && x[i] != 0) {
        return false;
      }
    }
    return true;
  }
}

static void MaxPool2dForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  auto& x = inputs.at(0);
  auto& y = outputs.at(0);
  std::string st_pool_size = attrs.dict.at("pool_size");
  std::string st_strides = attrs.dict.at("strides");
  std::string st_padding = attrs.dict.at("padding");
  std::string st_ceil_mode = attrs.dict.at("ceil_mode");
  Shape pool_size = Shape::from_string(st_pool_size);
  Shape strides = Shape::from_string(st_strides);
  Shape padding = Shape::from_string(st_padding);
  bool ceil_mode;
  std::istringstream(st_ceil_mode) >> std::boolalpha >> ceil_mode;
  const auto hidx = 2;
  const auto widx = 3;
  int tpad[2] = { padding.at(0), padding.at(0)};
  if(padding.size() == 2){
    tpad[1] = (int)padding[1];
  }

  int stride_h = strides[0];
  int stride_w = strides[1];

  int filter_h = pool_size[0];
  int filter_w = pool_size[1];

  int n_batch = static_cast<int>(x->shape[0]);
  int in_channels = static_cast<int>(x->shape[1]);
  int out_channels = in_channels;
  int x_h = static_cast<int>(x->shape[2]);
  int x_w = static_cast<int>(x->shape[3]);
  int o_h = static_cast<int>(y->shape[2]);
  int o_w = static_cast<int>(y->shape[3]);


    #define GETX(n, c, h, w) (n) * in_channels * x_h * x_w + (c) * x_h * x_w + (h) * x_w + (w)
    #define GETY(n, c, h, w) (n) * out_channels * o_h * o_w + (c) * o_h * o_w + (h) * o_w + (w)
    auto calc_func = [&](int n, int k, int p, int q) {
    const int32_t minV = int32_t(1) << 31;
    z3_expr y_max = minV;
    int idy = GETY(n, k, p, q);
    int uid = 0;
    for (int r = 0; r < filter_h; ++r) {
      for (int s = 0; s < filter_w; ++s) {
        int32_t tp = p * stride_h + r - padding[0];
        int32_t tq = q * stride_w + s - padding[1];
        z3_expr x_tmp = minV; 
        if (0 <= tp && tp < x_h && 0 <= tq && tq < x_w){
          int idx = GETX(n, k, tp, tq);
          x_tmp = x->at(idx);
          y_max = op_max(x_tmp, y_max);
          nas[0].at(idy).add_input(x, idx);
          uid++;
        }
      }
    }
    y->set_data(idy, y_max);
    nas[0].at(idy).add_output(y, idy).set_uid(uid);
    return uid;
  };
  for (int n = 0; n < n_batch; ++n) {
    for (int k = 0; k < out_channels; ++k) {
      for (int p = 0; p < o_h; ++p) {
        for (int q = 0; q < o_w; ++q) {
          calc_func(n, k, p, q);
        }
      }
    }
  }
}

static void MaxPool2dInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 1U);

  Shape dshape = ishpes.at(0);
  VERIFY (dshape.size() !=  0);

  VERIFY_EQ(dshape.size(), 4U)
    << "Pool2D only support input = 4-D: NCHW";
  
  std::string st_layout = attrs.dict.at("layout");
  VERIFY_EQ(st_layout, "NCHW")
    << "Pool2D only supported NCHW layout vs. " << st_layout;
  
  std::string st_pool_size = attrs.dict.at("pool_size");
  std::string st_strides = attrs.dict.at("strides");
  std::string st_padding = attrs.dict.at("padding");
  std::string st_ceil_mode = attrs.dict.at("ceil_mode");
  Shape pool_size = Shape::from_string(st_pool_size);
  Shape strides = Shape::from_string(st_strides);
  Shape padding = Shape::from_string(st_padding);
  bool ceil_mode;
  std::istringstream(st_ceil_mode) >> std::boolalpha >> ceil_mode;
  const auto hidx = 2;
  const auto widx = 3;
  
  int pad_h, pad_w;
  VERIFY(padding.size() == 1U || padding.size() == 2U)
    << "Pool2D only supported 1-D or 2-D padding vs. ";
  VERIFY(0 <= padding.at(0) && padding.at(0) < 4096);
  if (padding.size() == 1) {
    pad_h = padding.at(0) * 2;
    pad_w = padding.at(0) * 2;
  } else if (padding.size() == 2) {
    // (top, left)
    pad_h = padding.at(0) * 2;
    pad_w = padding.at(1) * 2;
    VERIFY(0 <= padding.at(1) && padding.at(1) < 4096);
  } 
  
  Shape oshape = dshape;
  VERIFY(pool_size.size() == 2);
  VERIFY(strides.size() == 2);
  VERIFY(1 <= strides.at(0) && strides.at(0) < 4096);
  VERIFY(1 <= strides.at(1) && strides.at(1) < 4096);

  VERIFY(1 <= pool_size.at(0) && pool_size.at(0) < dshape[hidx] + pad_h + 1);
  VERIFY(1 <= pool_size.at(1) && pool_size.at(1) < dshape[widx] + pad_w + 1);
  
  int tpad[2] = { padding.at(0), padding.at(0)};
  if(padding.size() == 2U){
    tpad[1] = padding.at(1);
  }

  VERIFY(tpad[0] < pool_size.at(0));
  VERIFY(tpad[1] < pool_size.at(1));
  
  
  if (!ceil_mode) {
    oshape[hidx] = ((dshape[hidx] + pad_h - pool_size[0]) /
                    strides[0]) + 1;
    oshape[widx] = ((dshape[widx] + pad_w - pool_size[1]) /
                    strides[1]) + 1;
  } else {
    oshape[hidx] = ((dshape[hidx] + pad_h - pool_size[0] +
                    strides[0] - 1) / strides[0]) + 1;
    int32_t min_o_h = (oshape[hidx]-1) * strides[0] - padding[0];
    VERIFY(min_o_h < dshape[hidx]);
    
    oshape[widx] = ((dshape[widx] + pad_w - pool_size[1] +
                    strides[1] - 1) / strides[1]) + 1;
    int32_t min_o_w = (oshape[widx]-1) * strides[1] - (padding.size() == 1 ? padding[0] : padding[1]);
    VERIFY(min_o_w < dshape[widx]);
  }
  oshpes.at(0) = oshape;
}

static void MaxPool2dInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  oprecs.at(0) = iprecs.at(0);
}

Z3_REGISTER_OP(max_pool2d)
  .set_num_inputs(kVarg)
  .set_num_outputs(1)
  .set_attr_default(MaxPool2dAttrDefault)
  .set_forward(MaxPool2dForward)
  .set_infer_shape(MaxPool2dInferShape)
  .set_infer_precision(MaxPool2dInferPrecision)
  .set_generator(prove_gen(op_max, prec_max));

}
}
