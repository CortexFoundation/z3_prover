#include "cvm/op.h"
#include "cvm/node.h"
#include "common.h"

namespace z3 {
namespace cvm {

using namespace z3::type;

static void NonMaxSuppressionAttrDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "max_output_size", "-1");
  ATTR_DEFAULT(attrs, "iou_threshold", "50");
  ATTR_DEFAULT(attrs, "force_suppress", "false");
  ATTR_DEFAULT(attrs, "top_k", "-1");
  ATTR_DEFAULT(attrs, "coord_start", "2");
  ATTR_DEFAULT(attrs, "score_index", "1");
  ATTR_DEFAULT(attrs, "id_index", "0");
  ATTR_DEFAULT(attrs, "return_indices", "false");
  ATTR_DEFAULT(attrs, "invalid_to_bottom", "true");
}

static void NonMaxSuppressionForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
 
    auto& x = inputs.at(0);
    auto& valid_count = inputs.at(1);
    auto& y = outputs.at(0);
    std::string const s_coord_start = attrs.dict.at("coord_start");
    int coord_start = std::stoi(s_coord_start);
    std::string const s_max_output_size = attrs.dict.at("max_output_size");
    int max_output_size = std::stoi(s_max_output_size);
    std::string const s_iou_threshold = attrs.dict.at("iou_threshold");
    int iou_threshold = std::stoi(s_iou_threshold);
    std::string const s_force_suppress = attrs.dict.at("force_suppress");
    bool force_suppress;
    std::istringstream(s_force_suppress) >> std::boolalpha >> force_suppress;
    std::string const s_top_k = attrs.dict.at("top_k");
    int top_k = std::stoi(s_top_k);
    std::string const s_score_index = attrs.dict.at("score_index");
    int score_index = std::stoi(s_score_index);
    std::string const s_id_index = attrs.dict.at("id_index");
    int id_index = std::stoi(s_id_index);
    std::string const s_return_indices = attrs.dict.at("return_indices");
    bool return_indices;
    std::istringstream(s_return_indices) >> std::boolalpha >> return_indices;
    std::string const s_invalid_to_bottom = attrs.dict.at("invalid_to_bottom");
    bool invalid_to_bottom;
    std::istringstream(s_invalid_to_bottom) >> std::boolalpha >> invalid_to_bottom;

    int32_t batchs = x->shape[0];
    int32_t n = x->shape[1];
    int32_t k = x->shape[2];

    //int ret = non_max_suppression(
    //        x, valid_count_data, y, batchs, n, k,
    //        max_output_size, iou_threshold, top_k, coord_start, score_index, id_index, force_suppress);
    //VERIFY(ret >= 0);
}

static void NonMaxSuppressionInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {

  VERIFY_EQ(ishpes.size(), 2U) << "Inputs: [data, valid_count]";
  Shape dshape = ishpes.at(0);
  Shape vshape = ishpes.at(1);
  VERIFY_EQ(dshape.size(), 3U) << "Input data should be 3-D.";
  VERIFY_EQ(vshape.size(), 1U) << "Input valid count should be 1-D.";
  VERIFY_EQ(dshape[2], 6U) << "Data input should have shape "
    "(batch_size, num_anchors, 6).";
  VERIFY_EQ(dshape[0], vshape[0]) << "batch_size mismatch.";
 
  std::string const s_coord_start = attrs.dict.at("coord_start");
  int coord_start = std::stoi(s_coord_start);
  std::string const s_max_output_size = attrs.dict.at("max_output_size");
  int max_output_size = std::stoi(s_max_output_size);
  std::string const s_iou_threshold = attrs.dict.at("iou_threshold");
  int iou_threshold = std::stoi(s_iou_threshold);
  std::string const s_force_suppress = attrs.dict.at("force_suppress");
  bool force_suppress;
  std::istringstream(s_force_suppress) >> std::boolalpha >> force_suppress;
  std::string const s_top_k = attrs.dict.at("top_k");
  int top_k = std::stoi(s_top_k);
  std::string const s_score_index = attrs.dict.at("score_index");
  int score_index = std::stoi(s_score_index);
  std::string const s_id_index = attrs.dict.at("id_index");
  int id_index = std::stoi(s_id_index);
  std::string const s_return_indices = attrs.dict.at("return_indices");
  bool return_indices;
  std::istringstream(s_return_indices) >> std::boolalpha >> return_indices;
  std::string const s_invalid_to_bottom = attrs.dict.at("invalid_to_bottom");
  bool invalid_to_bottom;
  std::istringstream(s_invalid_to_bottom) >> std::boolalpha >> invalid_to_bottom;

  VERIFY(coord_start == 2);
  VERIFY(score_index == 1);
  VERIFY(id_index == 0);
  VERIFY(iou_threshold > 0);

  VERIFY_EQ(return_indices, false)
    << "NonMaximumSuppressionParam only supported return_indices false vs. "
    << return_indices;
  VERIFY_EQ(invalid_to_bottom, true)
    << "NonMaximumSuppressionParam only supported invalid_to_bottom false vs. "
    << invalid_to_bottom;
  if (return_indices) {
    Shape oshape = Shape(2);
    oshape[0] = dshape[0];
    oshape[1] = dshape[1];
    oshpes.at(0) = oshape;
  } else {
    oshpes.at(0) = dshape;
  }
}

static void NonMaxSuppressionInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {

  oprecs[0] = iprecs.at(0);

}

Z3_REGISTER_OP(non_max_suppression)
  .set_num_inputs(2)
  .set_num_outputs(1)
  .set_attr_default(NonMaxSuppressionAttrDefault)
  .set_forward(NonMaxSuppressionForward)
  .set_infer_shape(NonMaxSuppressionInferShape)
  .set_infer_precision(NonMaxSuppressionInferPrecision)
  .set_generator(null_generator);

static void GetValidCountsAttrDefault(NodeAttrs& attrs) {
  ATTR_DEFAULT(attrs, "score_threshold", "0");
}

static void GetValidCountsForward(
    NodeAttrs const& attrs,
    std::vector<TypePtr>& inputs,
    std::vector<TypePtr>& outputs,
    std::vector<std::vector<NodeAssertions> >& nas) {
    auto& x = inputs.at(0);
    auto& valid_count = outputs.at(0);
    auto& y = outputs.at(1);
    
    std::string const s_score_threthold = attrs.dict.at("score_threshold");
    int score_threshold = std::stoi(s_score_threthold);
    
    int32_t batchs = x->shape[0];
    int32_t n = x->shape[1];
    int32_t k = x->shape[2];
    
  
 // get_valid_count(x_data, y_data, valid_count_data, batches, n, k, score_threshold);
}

static void GetValidCountsInferShape(
    NodeAttrs const& attrs,
    std::vector<Shape> &ishpes,
    std::vector<Shape> &oshpes) {
  Shape shp = ishpes.at(0);
  VERIFY_EQ(ishpes.size(), 1U);
  VERIFY_EQ(oshpes.size(), 2U);
  VERIFY(shp.size() == 3);
  VERIFY(shp[2] >= 2);
  Shape count_shape{shp[0]};
  Shape oshape(shp);
  oshpes.at(0) = count_shape;
  oshpes.at(1) = oshape;
}

static void GetValidCountsInferPrecision(
    NodeAttrs const& attrs,
    std::vector<type::Shape> &ishpes,
    std::vector<type::z3_expr> &iprecs,
    std::vector<type::z3_expr> &oprecs,
    std::vector<NodeAssertions> &nas) {

  const auto& shp = ishpes.at(0);
  int64_t inl = shp.Size() / shp[0];
  auto oprec1 = GetBit(inl);
  oprecs.at(0) = oprec1;
  oprecs.at(1) = iprecs.at(0);

}

Z3_REGISTER_OP(get_valid_counts)
  .set_num_inputs(1)
  .set_num_outputs(2)
  .set_attr_default(GetValidCountsAttrDefault)
  .set_forward(GetValidCountsForward)
  .set_infer_shape(GetValidCountsInferShape)
  .set_infer_precision(GetValidCountsInferPrecision)
  .set_generator(null_generator);

}
}
