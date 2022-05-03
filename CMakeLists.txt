cmake_minimum_required(VERSION 3.1.0)

# FIXME: Unfortunately, C is (at least temporarily) required due to a bug
# in LLVM 14.  See https://github.com/llvm/llvm-project/issues/53950.
project(sbt-slicer LANGUAGES C CXX)

# --------------------------------------------------
# Build type
# --------------------------------------------------
if(NOT CMAKE_BUILD_TYPE)
  message(STATUS "Build type not set. Setting default.")
  set(CMAKE_BUILD_TYPE "RelWithDebInfo" CACHE STRING "" FORCE)
endif()
message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")
set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "Debug" "RelWithDebInfo"
                                                     "MinSizeRel" "Release")

# --------------------------------------------------
# Compiler flags
# --------------------------------------------------
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti -Wall -Wextra -pedantic")

# --------------------------------------------------
# LLVM
# --------------------------------------------------
find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "LLVM definitions: ${LLVM_DEFINITIONS}")
message(STATUS "LLVM include dir: ${LLVM_INCLUDE_DIRS}")
message(STATUS "LLVM libraries dir: ${LLVM_LIBRARY_DIRS}")

list(APPEND CMAKE_MODULE_PATH "${LLVM_DIR}")
include(AddLLVM)

# TODO: move this to the section above when we switch to C++14
# LLVM 10 and newer require at least C++14 standard
if (${LLVM_PACKAGE_VERSION} VERSION_GREATER "9.0")
  set(CMAKE_CXX_STANDARD 14)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14")
else()
  # otherwise we need C++11 standard
  set(CMAKE_CXX_STANDARD 11)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
endif()

include_directories(SYSTEM ${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})
add_definitions(${LLVM_DEFINITIONS})

option(LLVM_LINK_DYLIB "Link with LLVM dynamically" ON)
if (LLVM_LINK_DYLIB)
  message(STATUS "LLVM linking: dynamic")
  if (${LLVM_PACKAGE_VERSION} VERSION_LESS "3.8")
    set(LLVM_LIBS LLVM-${LLVM_PACKAGE_VERSION})
  else()
    # only LLVM 3.8+ provide unversioned library
    set(LLVM_LIBS LLVM)
  endif()
else()
  message(STATUS "LLVM linking: static")
  if (NOT ${LLVM_PACKAGE_VERSION} VERSION_LESS "3.4")
    llvm_map_components_to_libnames(LLVM_LIBS analysis bitwriter core irreader
                                              support)
  else()
    llvm_map_components_to_libraries(LLVM_LIBS analysis bitwriter core irreader
                                               support)
  endif()
endif()

# --------------------------------------------------
# DG
# --------------------------------------------------

# enable CFG and LLVM in dg
add_definitions(-DENABLE_CFG)
add_definitions(-DHAVE_LLVM)

if(NOT DG_INCLUDE_PATH)
  set(DG_INCLUDE_PATH ${CMAKE_SOURCE_DIR}/dg/include ${CMAKE_SOURCE_DIR}/dg/tools/include)
endif()

if(NOT DG_LIB_PATH)
  set(DG_LIB_PATH ${CMAKE_SOURCE_DIR}/dg/lib)
endif()

# DG_PATH is a path to an in-source build of dg
if (DG_PATH)
  message(STATUS "Setting-up paths to an in-source build of dg")
  set(DG_INCLUDE_PATH ${DG_PATH}/include ${DG_PATH}/tools/include)
  set(DG_LIB_PATH ${DG_PATH}/lib ${DG_PATH}/tools)
endif()

message(STATUS "DG include paths: ${DG_INCLUDE_PATH}")
message(STATUS "DG library paths: ${DG_LIB_PATH}")

include_directories(${DG_INCLUDE_PATH})
link_directories(${DG_LIB_PATH})

# TODO: Maybe we could make a DG CMake package and then just use find_package?
macro(find_dg_library lib)
  find_library(lib${lib} ${lib} PATHS ${DG_LIB_PATH} ${DG_LIB_PATH}/../tools)
  if(lib${lib})
    message(STATUS "lib${lib} library found: ${lib${lib}}")
  else()
    message(FATAL_ERROR "lib${lib} library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
  endif()
  list(APPEND DG_LIBS ${lib${lib}})
endmacro()

foreach(lib dganalysis dgpta dgdda dgllvmpta dgllvmdda dgllvmdg dgllvmcda
            dgllvmthreadregions dgllvmslicer)
  find_dg_library(${lib})
endforeach()

# --------------------------------------------------
# Set correct install directories
# --------------------------------------------------
include(GNUInstallDirs)
message(STATUS "CMAKE_INSTALL_BINDIR: \"${CMAKE_INSTALL_BINDIR}\"")

# --------------------------------------------------
# Subdirectories
# --------------------------------------------------
add_subdirectory(src)
