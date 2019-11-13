cmake_minimum_required(VERSION 3.14)
project(z3_prover CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(CMAKE_CXX_FLAGS "-g -std=c++11")
set(Z3_DIR "${CMAKE_CURRENT_SOURCE_DIR}/3rdparty/z3")

include_directories("include")
include_directories("${Z3_DIR}/src/api")
include_directories("${Z3_DIR}/src/api/c++")

file(GLOB Z3_PROVER_SRCS 
      src/main.cc
      src/cvm/core/*.cc
      src/cvm/top/*.cc
      src/cvm/top/*/*.cc)

add_executable(${PROJECT_NAME} ${Z3_PROVER_SRCS})

# find_package(Z3
  # REQUIRED
  # CONFIG
  # # `NO_DEFAULT_PATH` is set so that -DZ3_DIR has to be passed to find Z3.
  # # This should prevent us from accidentally picking up an installed
  # # copy of Z3. This is here to benefit Z3's build system when building
  # # this project. When making your own project you probably shouldn't
  # # use this option.
  # NO_DEFAULT_PATH
# )
# message(STATUS "Z3_FOUND: ${Z3_FOUND}")
# message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
# message(STATUS "Z3_DIR: ${Z3_DIR}")
target_link_libraries(${PROJECT_NAME} "${Z3_DIR}/build/libz3.so")
