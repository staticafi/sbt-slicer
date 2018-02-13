cmake_minimum_required(VERSION 2.8.8)
project(sbt-slicer)

# Compiler Options
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -std=c++11 -Wall -Wextra -Wno-unused-variable")

find_package(LLVM REQUIRED CONFIG)
if (${LLVM_PACKAGE_VERSION} VERSION_GREATER "3.4")
  set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${LLVM_DIR}")
  include(LLVMConfig)
endif()
include(AddLLVM)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

if (LLVM_SRC_PATH)
  include_directories(${LLVM_SRC_PATH}/include)
  SET(LLVM_INCLUDE_DIRS ${LLVM_SRC_PATH}/include)
  message(STATUS "Got LLVM_SRC_PATH ${LLVM_SRC_PATH}")
endif(LLVM_SRC_PATH)
if (LLVM_BUILD_PATH)
  include_directories(${LLVM_BUILD_PATH}/include)
  link_directories(${LLVM_BUILD_PATH}/lib)
  SET(LLVM_LIBRARY_DIRS ${LLVM_BUILD_PATH}/lib)
  message(STATUS "Got LLVM_BUILD_PATH ${LLVM_BUILD_PATH}")
endif(LLVM_BUILD_PATH)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "LLVM include dir: ${LLVM_INCLUDE_DIRS}")
message(STATUS "LLVM libraries dir: ${LLVM_LIBRARY_DIRS}")
message(STATUS "LLVM definitions: ${LLVM_DEFINITIONS}")

add_definitions(-DHAVE_LLVM)
# enable CFG in dg
add_definitions(-DENABLE_CFG)

# Find the libraries that correspond to the LLVM components
# that we wish to use
if (${LLVM_PACKAGE_VERSION} VERSION_GREATER "3.4")
  llvm_map_components_to_libnames(llvm_libs support core irreader bitwriter)
else()
  llvm_map_components_to_libraries(llvm_libs support core irreader bitwriter)
endif()

if (DG_PATH)
	include_directories(${DG_PATH}/src/)
else()
	set(DG_PATH ${CMAKE_SOURCE_DIR}/dg)
	include_directories(${CMAKE_SOURCE_DIR}/dg/src)
endif()

find_library(LIBPTA PTA PATHS ${DG_PATH}/src/)
find_library(LIBRD RD PATHS ${DG_PATH}/src/)
find_library(LIBLLVMPTA LLVMpta PATHS ${DG_PATH}/src/)
find_library(LIBLLVMDG LLVMdg PATHS ${DG_PATH}/src/)

if (LIBPTA)
	message(STATUS "libPTA library found: ${LIBPTA}")
else()
	message(FATAL_ERROR
	        "libPTA library NOT found! Try specifying -DDG_PATH=<path>.")
endif()

if (LIBRD)
	message(STATUS "libRD library found: ${LIBRD}")
else()
	message(FATAL_ERROR
	        "libRD library NOT found! Try specifying -DDG_PATH=<path>.")
endif()

if (LIBLLVMPTA)
	message(STATUS "libLLVMPTA library found: ${LIBLLVMPTA}")
else()
	message(FATAL_ERROR
	        "libLLVMPTA library NOT found! Try specifying -DDG_PATH=<path>.")
endif()

if (LIBLLVMDG)
	message(STATUS "LLVMdg library found: ${LIBLLVMDG}")
else()
	message(FATAL_ERROR
	        "LLVMdg library NOT found! Try specifying -DDG_PATH=<path>.")
endif()

set(dg_libs ${LIBPTA} ${LIBRD} ${LIBLLVMPTA} ${LIBLLVMDG})

include(GNUInstallDirs)
message(STATUS "CMAKE_INSTALL_LIBDIR: \"${CMAKE_INSTALL_LIBDIR}\"")
message(STATUS "CMAKE_INSTALL_DATADIR: \"${CMAKE_INSTALL_FULL_DATADIR}\"")

enable_testing()

add_subdirectory(src)
#add_subdirectory(tests)
