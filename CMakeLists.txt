cmake_minimum_required(VERSION 2.8.8)
project(sbt-slicer)

# we need C++11 standard
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED on)

# Compiler Options
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti -std=c++11 -Wall -Wextra")

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "LLVM binaries: ${LLVM_TOOLS_BINARY_DIR}")

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${LLVM_DIR}")
include(LLVMConfig)
include(AddLLVM)

message(STATUS "LLVM include dir: ${LLVM_INCLUDE_DIRS}")
message(STATUS "LLVM libraries dir: ${LLVM_LIBRARY_DIRS}")
message(STATUS "LLVM definitions: ${LLVM_DEFINITIONS}")

include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

# if we were provided a path to custom sources use that path
if (LLVM_SRC_PATH)
  include_directories(${LLVM_SRC_PATH}/include)
  message(STATUS "Looking for LLVM headers in given: ${LLVM_SRC_PATH}/include")
else()
  include_directories(${LLVM_INCLUDE_DIRS})
  message(STATUS "Looking for LLVM headers in: ${LLVM_INCLUDE_DIRS}")
endif()

# if we were provided a path to custom build directory
# use that
if (LLVM_BUILD_PATH)
  link_directories(${LLVM_BUILD_PATH}/lib)

  # llvm-config.h
  include_directories("${LLVM_BUILD_PATH}/include")
  message(STATUS "Looking for libraries in given: ${LLVM_BUILD_PATH}/lib")
else()
  link_directories(${LLVM_LIBRARY_DIRS})
  message(STATUS "Looking for libraries in: ${LLVM_LIBRARY_DIRS}")
endif(LLVM_BUILD_PATH)

add_definitions(${LLVM_DEFINITIONS})

if (NOT ${LLVM_PACKAGE_VERSION} VERSION_LESS "3.4")
	llvm_map_components_to_libnames(llvm_libs support core
	                                irreader bitwriter analysis)
else()
	llvm_map_components_to_libraries(llvm_libs support core
	                                 irreader bitwriter analysis)
endif()

# enable CFG and LLVM in dg
add_definitions(-DENABLE_CFG)
add_definitions(-DHAVE_LLVM)

if(DG_INCLUDE_PATH)
else()
	set(DG_INCLUDE_PATH ${CMAKE_SOURCE_DIR}/dg/src)
endif()

if(DG_LIB_PATH)
else()
	set(DG_LIB_PATH ${CMAKE_SOURCE_DIR}/dg/src)
endif()

# DG_PATH is a path to an in-source build of dg
if (DG_PATH)
	message(STATUS "Setting-up paths to an in-source build of dg")
	set(DG_INCLUDE_PATH ${DG_PATH}/src)
	set(DG_LIB_PATH ${DG_PATH}/src)
endif()

message(STATUS "DG include paths: ${DG_INCLUDE_PATH}")
message(STATUS "DG library paths: ${DG_LIB_PATH}")

include_directories(${DG_INCLUDE_PATH})
link_directories(${DG_LIB_PATH})

find_library(LIBDGANALYSIS DGAnalysis PATH ${DG_LIB_PATH})
find_library(LIBPTA PTA PATH ${DG_LIB_PATH})
find_library(LIBRD RD PATH ${DG_LIB_PATH})
find_library(LIBLLVMPTA LLVMpta PATH ${DG_LIB_PATH})
find_library(LIBLLVMRD LLVMrd PATH ${DG_LIB_PATH})
find_library(LIBLLVMDG LLVMdg PATH ${DG_LIB_PATH})

if (LIBDGANALYSIS)
	message(STATUS "libDGAnalysis library found: ${LIBDGANALYSIS}")
else()
	message(FATAL_ERROR
	        "libDGAnalysis library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()

if (LIBPTA)
	message(STATUS "libPTA library found: ${LIBPTA}")
else()
	message(FATAL_ERROR
	        "libPTA library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()

if (LIBRD)
	message(STATUS "libRD library found: ${LIBRD}")
else()
	message(FATAL_ERROR
	        "libRD library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()

if (LIBLLVMPTA)
	message(STATUS "libLLVMPTA library found: ${LIBLLVMPTA}")
else()
	message(FATAL_ERROR
	        "libLLVMPTA library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()

if (LIBLLVMRD)
	message(STATUS "LLVMrd library found: ${LIBLLVMRD}")
else()
	message(FATAL_ERROR
	        "LLVMrd library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()

if (LIBLLVMDG)
	message(STATUS "LLVMdg library found: ${LIBLLVMDG}")
else()
	message(FATAL_ERROR
	        "LLVMdg library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()

set(dg_libs ${LIBDGANALYSIS} ${LIBPTA} ${LIBRD}
	    ${LIBLLVMPTA} ${LIBLLVMRD} ${LIBLLVMDG})

include(GNUInstallDirs)
message(STATUS "CMAKE_INSTALL_LIBDIR: \"${CMAKE_INSTALL_LIBDIR}\"")
message(STATUS "CMAKE_INSTALL_DATADIR: \"${CMAKE_INSTALL_FULL_DATADIR}\"")

enable_testing()

add_subdirectory(src)
#add_subdirectory(tests)
