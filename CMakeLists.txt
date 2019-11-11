cmake_minimum_required(VERSION 3.14)
project(z3_prover CXX)

set(Z3_LIBS "z3")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(CMAKE_CXX_FLAGS "-std=c++11")

include_directories("include")

file(GLOB Z3_PROVER_SRCS 
      src/main.cc
      src/cvm/top/*.cc
      src/cvm/top/*/*.cc)

add_executable(${PROJECT_NAME} ${Z3_PROVER_SRCS})

link_directories("./3rdparty/z3/build")
target_link_libraries(${PROJECT_NAME} ${Z3_LIBS})
