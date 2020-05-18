#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

uint32_t UseBiasNumInputsConv2d(const NodeAttrs& attrs) {
  return attrs.dict.at("use_bias") == "true" ? 3 : 2;
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

static void Conv2dAttrDefault(NodeAttrs& attrs) {
  ATTR_DECL(attrs, "channels");
  ATTR_DECL(attrs, "kernel_size");
  ATTR_DEFAULT(attrs, "strides", "(1, 1)");
  ATTR_DEFAULT(attrs, "padding", "(0, 0)");
  ATTR_DEFAULT(attrs, "dilation", "(1, 1)");
  ATTR_DEFAULT(attrs, "groups", "1");
  ATTR_DEFAULT(attrs, "layout", "NCHW");
  ATTR_DEFAULT(attrs, "out_layout", "__undef__");
  ATTR_DEFAULT(attrs, "kernel_layout", "OIHW");
  ATTR_DEFAULT(attrs, "out_dtype", "-1");
  ATTR_DEFAULT(attrs, "use_bias", "true");
}

void groupwise_conv2d(
   TypePtr& x, int32_t n_batch, int32_t in_channels, int32_t x_h, int32_t x_w,
   TypePtr& w, int32_t filter_c, int32_t filter_h, int32_t filter_w,
   TypePtr& y, int32_t out_channels, int32_t o_h, int32_t o_w,
   TypePtr& b,
   int32_t padding[2], int32_t stride_h, int32_t stride_w, int32_t dilation_h, int32_t dilation_w,
   int32_t groups, bool use_bias, std::vector<std::vector<NodeAssertions> >& nas){
  int32_t ochannels_per_group = out_channels / groups;
  int32_t ichannels_per_group = in_channels / groups;
  for(int32_t n = 0; n < n_batch; ++n){
    for(int32_t oc = 0; oc < out_channels; ++oc){
      for(int32_t oh = 0; oh < o_h; ++oh){
        for(int32_t ow = 0; ow < o_w; ++ow){
          int32_t oi = n * out_channels * o_h * o_w + oc * o_h * o_w + oh * o_w + ow;
          z3_expr sum = 0;
          int32_t ic = oc / ochannels_per_group * ichannels_per_group;
          for(int32_t tic = 0; tic < ichannels_per_group; ++tic){
            for(int32_t fh = 0; fh < filter_h; ++fh){
              for(int32_t fw = 0; fw < filter_w; ++fw){
                int32_t th = oh * stride_h + fh*dilation_h - padding[0];
                int32_t tw = ow * stride_w + fw*dilation_w - padding[1];
                if(th < 0 || tw < 0 || th >= x_h || tw >= x_w)
                  continue;
                int32_t xi = n * in_channels * x_h * x_w + (ic+tic) * x_h * x_w + th * x_w + filter_w;
                int32_t wi = oc * filter_c * filter_h * filter_w + tic * filter_h * filter_w + fh * filter_w + fw;
                sum = sum + x->at(xi) * w->at(wi);
                nas[0].at(oi)
                  .add_input(x, xi)
                  .add_input(w, wi);
              }
            }
          }
          if (use_bias){
            y->set_data(oi, sum + b->at(oc));
            nas[0].at(oi)
              .add_input(b, oc)
              .add_output(y, oi);
          }else {
            y->set_data(oi, sum);
            nas[0].at(oi)
              .add_output(y, oi);
          }
        }
      }
    }
  }
}

inline bool is_a_ge_zero_and_a_lt_b(int a, int b) {
  return static_cast<unsigned>(a) < static_cast<unsigned>(b);
}

void im2col_cpu(const TypePtr& data_im, const int channels,
    const int height, const int width, const int kernel_h, const int kernel_w,
    const int pad_h, const int pad_w,
    const int stride_h, const int stride_w,
    const int dilation_h, const int dilation_w,
    std::vector<z3_expr>& data_col, std::vector<int>& data_col_index, bool &has_negetive, int base_index)
{
  // auto data_col_init = data_col;
  const int output_h = (height + 2 * pad_h -
      (dilation_h * (kernel_h - 1) + 1)) / stride_h + 1;
  const int output_w = (width + 2 * pad_w -
      (dilation_w * (kernel_w - 1) + 1)) / stride_w + 1;
  const int channel_size = height * width;
  int index = 0, index_col = 0;
  for (int channel = channels; channel--; index += channel_size) {
    for (int kernel_row = 0; kernel_row < kernel_h; kernel_row++) {
      for (int kernel_col = 0; kernel_col < kernel_w; kernel_col++) {
        int input_row = -pad_h + kernel_row * dilation_h;
        for (int output_rows = output_h; output_rows; output_rows--) {
          if (!is_a_ge_zero_and_a_lt_b(input_row, height)) {
            for (int output_cols = output_w; output_cols; output_cols--) {
              data_col.at(index_col++) = 0;
            }
          } else {
            int input_col = -pad_w + kernel_col * dilation_w;
            for (int output_col = output_w; output_col; output_col--) {
              if (is_a_ge_zero_and_a_lt_b(input_col, width)) {
                auto tv = data_im->at(base_index + index + input_row * width + input_col);
                //if(tv < 0) {
                //  has_negetive = true;
                //}
                data_col_index.at(index_col) = base_index + index + input_row * width + input_col;
                data_col.at(index_col++) = tv;
              } else {
                data_col.at(index_col++) = 0;
              }
              input_col += stride_w;
            }
          }
          input_row += stride_h;
        }
      }
    }
  }
}

void matrix_mul(std::vector<z3_expr>& a, const std::vector<int>& a_index, TypePtr& w,
    std::vector<z3_expr>& b, const std::vector<int>& b_index, TypePtr& x,
    const TypePtr& bias, bool use_bias, TypePtr& y, int base_index, const int M,
    const int K, const int N, std::vector<std::vector<NodeAssertions> >& nas, 
    int algo = 0)
{
     for(int i = 0; i < M; i++){
        for(int j = 0; j < N; j++){
         z3_expr y_sum = 0;
        int yid = i * N + j + base_index; 
          for(int k = 0; k < K; k++){
             auto aV = a.at(i * K + k);
               y_sum = y_sum + aV * b.at(k * N + j); 
                if (a_index.at(i * K + k) != -1){
                  nas[0].at(yid)
                    .add_input(w, a_index.at(i * K + k));
                }

                if (b_index.at(k * N + j) != -1){
                  nas[0].at(yid)
                    .add_input(x, b_index.at(k * N + j));
                }
             }
         if(use_bias){
            y_sum = y_sum + bias->at(i);
            nas[0].at(yid)
            .add_input(bias, i);
         }
         y->set_data(yid, y_sum);
          nas[0].at(yid).add_output(y, yid);
         }
     }

}

static void Conv2dForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
  TypePtr& x = inputs.at(0);
  TypePtr& w = inputs.at(1);
  TypePtr b;
  TypePtr& y = outputs.at(0);
  std::string const s_use_bias = attrs.dict.at("use_bias");
  bool use_bias;
  std::istringstream(s_use_bias) >> std::boolalpha >> use_bias;
  if (use_bias) {
    b = inputs.at(2);
  }
  std::string const s_kernel_size = attrs.dict.at("kernel_size");
  Shape kernel_size = Shape::from_string(s_kernel_size);
  std::string const s_padding = attrs.dict.at("padding");
  Shape padding_shape = Shape::from_string(s_padding);
  std::string const s_strides = attrs.dict.at("strides");
  Shape strides_shape = Shape::from_string(s_strides);
  std::string const s_dilation = attrs.dict.at("dilation");
  Shape dilation_shape = Shape::from_string(s_dilation);
  std::string const s_groups = attrs.dict.at("groups");
  std::string const s_channels = attrs.dict.at("channels");
  int groups = std::stoi(s_groups);
  int channels = std::stoi(s_channels);
  
  
  int dilation[2] = {(int)dilation_shape[0], (int)dilation_shape[1]};
  // int kernel_size[2] = {(int)param.kernel_size[0], (int)param.kernel_size[1]};
  int padding[2] = {(int)padding_shape[0], (int)padding_shape[1]};
  int strides[2] = {(int)strides_shape[0], (int)strides_shape[1]};

  int stride_h = strides[0];
  int stride_w = strides[1];
  int dilation_h = dilation[0];
  int dilation_w = dilation[1];

  int out_channels = static_cast<int>(w->shape[0]);
  int filter_c = static_cast<int>(w->shape[1]);
  int filter_h = static_cast<int>(w->shape[2]);
  int filter_w = static_cast<int>(w->shape[3]);
  int t_filter_h = (filter_h - 1) * dilation[0] + 1;
  int t_filter_w = (filter_w - 1) * dilation[1] + 1;

  int n_batch = static_cast<int>(x->shape[0]);
  int in_channels = static_cast<int>(x->shape[1]);
  int x_h = static_cast<int>(x->shape[2]);
  int x_w = static_cast<int>(x->shape[3]);
  int o_h = (x_h + 2 * padding[0] - t_filter_h) / strides[0] + 1;
  int o_w = (x_w + 2 * padding[1] - t_filter_w) / strides[1] + 1;
  
  
  if(groups > 1){
    groupwise_conv2d(
        x, n_batch, in_channels, x_h, x_w,
        w, filter_c, filter_h, filter_w,
        y, out_channels, o_h, o_w,
        b,
        padding, stride_h, stride_w, dilation[0], dilation[1],
        groups, use_bias, nas);
  } else {
    int tmp_index = in_channels * filter_h * filter_w * o_h * o_w;
    std::vector<z3_expr> data_col;
    for (int i = 0; i < tmp_index; i++){
      data_col.push_back(0);
    }
    std::vector<int> data_col_index(tmp_index);
    for (auto& it : data_col_index){
      it = -1;
    }
    int32_t fn = out_channels * in_channels * filter_h * filter_w;
    std::vector<z3_expr> int8_filter;
    for (int i = 0; i < fn; i++){
      int8_filter.push_back(0);
    }
    std::vector<int> int8_filter_index(fn);
    for (auto& it : int8_filter_index){
      it = -1;
    }
    for(int32_t i = 0; i < fn; i++){
      int8_filter.at(i) = w->at(i);
      int8_filter_index.at(i) = i;
    }
    for(int32_t i = 0; i < n_batch; i++){
      bool has_negetive = false;
      im2col_cpu(x, in_channels, x_h, x_w, filter_h, filter_w, padding[0], padding[1],
          stride_h, stride_w, dilation_h, dilation_w, data_col, data_col_index, has_negetive, i * in_channels * x_h * x_w);
      const int32_t M = out_channels;
      const int32_t K = in_channels * filter_h * filter_w;
      const int32_t N = o_h * o_w;
      matrix_mul(int8_filter, int8_filter_index, w, 
          data_col, data_col_index, x, b, use_bias, 
          y, i * out_channels * o_h * o_w, M, K, N, nas);
    }
  }
}

static void Conv2dInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  std::string const layout = attrs.dict.at("layout");
  std::string const kernel_layout = attrs.dict.at("kernel_layout");
  
  VERIFY_EQ(layout, "NCHW")
    << "Conv2D only supported layout: NCHW vs. " << layout;
  VERIFY_EQ(kernel_layout, "OIHW")
    << "Conv2D only supported kernel layout: OIHW vs. " << kernel_layout;
  
  std::string const s_use_bias = attrs.dict.at("use_bias");
  bool use_bias;
  std::istringstream(s_use_bias) >> std::boolalpha >> use_bias;
  if (use_bias) {
    VERIFY_EQ(ishpes.size(), 3U) << "Input:[data, weight, bias]";
  } else {
    VERIFY_EQ(ishpes.size(), 2U) << "Input:[data, weight]";
  }
  VERIFY_EQ(oshpes.size(), 1U);
  
  std::string const s_kernel_size = attrs.dict.at("kernel_size");
  Shape kernel_size = Shape::from_string(s_kernel_size);
  std::string const s_padding = attrs.dict.at("padding");
  Shape padding = Shape::from_string(s_padding);
  std::string const s_strides = attrs.dict.at("strides");
  Shape strides = Shape::from_string(s_strides);
  std::string const s_dilation = attrs.dict.at("dilation");
  Shape dilation = Shape::from_string(s_dilation);
  std::string const s_groups = attrs.dict.at("groups");
  std::string const s_channels = attrs.dict.at("channels");
  int groups = std::stoi(s_groups);
  int channels = std::stoi(s_channels);

  Shape dshape = ishpes.at(0);
  VERIFY (dshape.size() != 0);

  VERIFY_EQ(dshape.size(), 4U) << "Input data should be 4D";
  VERIFY_EQ(kernel_size.size(), 2U);
  VERIFY_EQ(padding.size(), 2U);
  VERIFY(0 <= padding[0] && padding[0] < 4096);
  VERIFY(0 <= padding[1] && padding[1] < 4096);
  VERIFY_EQ(strides.size(), 2U)
      << "incorrect stride size: ";
  VERIFY(1 <= strides[0] && strides[1] < 4096);
  VERIFY(1 <= strides[1] && strides[1] < 4096);
  VERIFY_EQ(dilation.size(), 2U)
      << "incorrect dilate size: ";
  VERIFY(1 <= dilation[0] && dilation[0] < 4096);
  VERIFY(1 <= dilation[1] && dilation[1] < 4096);
  
  VERIFY(groups > 0 && dshape[1] % groups == 0 && 
            channels % groups == 0)
    << "Conv2D only supported groups (1 or in_channels " << channels
    << ") vs. " << groups;

  Shape wshape({channels,
                 dshape[1] / groups,
                 kernel_size[0],
                 kernel_size[1]});

  static const constexpr int kData = 0;
  static const constexpr int kWeight = 1;
  static const constexpr int kBias = 2;
  if (ishpes.at(kWeight).size() == 0) {
    wshape = ishpes.at(kWeight);
  }
  if (use_bias) {
    Shape bias_shape({channels});
    ishpes.at(kBias) = bias_shape;
  }
  
  int dilated_ksize_y = 1 + (kernel_size[0] - 1) * dilation[0];
  int dilated_ksize_x = 1 + (kernel_size[1] - 1) * dilation[1];
  Shape oshape({dshape[0], channels, 0, 0});
  if (dshape[2] != 0) {
    oshape[2] = (dshape[2] + padding[0] * 2 - dilated_ksize_y) / strides[0] + 1;
  }
  if (dshape[3] != 0) {
    oshape[3] = (dshape[3] + padding[1] * 2 - dilated_ksize_x) / strides[1] + 1;
  }
  oshpes.at(0) = oshape; 
  dshape[0] = oshape[0];
  if (oshape[2] && strides[0] == 1) {
    dshape[2] = oshape[2] + dilated_ksize_y - 1 - 2 * padding[0];
  }
  if (oshape[3] && strides[1] == 1) {
    dshape[3] = oshape[3] + dilated_ksize_x - 1 - 2 * padding[1];
  }
  ishpes.at(kData) = dshape;
  if (dshape[2] != 0) {
    VERIFY(dilated_ksize_y <= dshape[2] + 2 * padding[0])
      << "kernel size exceed input";
  }
  if (dshape[3] != 0) {
    VERIFY(dilated_ksize_x <=  dshape[3] + 2 * padding[1])
        << "kernel size exceed input";
  }
}

static void Conv2dInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {
  const Shape& wshp = ishpes.at(1);
  VERIFY_EQ(wshp.size(), 4);
  int64_t max_size = wshp.Size() / wshp[0];
  auto oprec = iprecs.at(0) + iprecs.at(1);
  oprec = oprec + GetBit(max_size);
  std::string const s_use_bias = attrs.dict.at("use_bias");
  bool use_bias;
  std::istringstream(s_use_bias) >> std::boolalpha >> use_bias;

  if (use_bias) {
    auto bias_prec = iprecs.at(2);
    oprec = type::op_max(oprec, bias_prec) + 1;
  }
  oprecs.at(0) = oprec;
}

Z3_REGISTER_OP(conv2d)
  .set_num_inputs(UseBiasNumInputsConv2d)
  .set_num_outputs(1)
  .set_attr_default(Conv2dAttrDefault)
  .set_forward(Conv2dForward)
  .set_infer_shape(Conv2dInferShape)
  .set_infer_precision(Conv2dInferPrecision)
  .set_generator(null_generator);


}
}
