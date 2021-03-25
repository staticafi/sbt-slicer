cmake_minimum_required(VERSION 3.1.0)
project(sbt-slicer)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "LLVM binaries: ${LLVM_TOOLS_BINARY_DIR}")

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${LLVM_DIR}")
include(LLVMConfig)
include(AddLLVM)

# LLVM 10 and newer require at least C++14 standard
if (${LLVM_PACKAGE_VERSION} VERSION_GREATER "9.0")
  set(CMAKE_CXX_STANDARD 14)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14")
else()
  # otherwise we need C++11 standard
  set(CMAKE_CXX_STANDARD 11)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
endif()
set(CMAKE_CXX_STANDARD_REQUIRED on)

# Compiler Options
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti -Wall -Wextra")

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

option(LLVM_LINK_DYLIB "Link with LLVM dynamically" ON)
if (LLVM_LINK_DYLIB)
	message(STATUS "LLVM linking: dynamic")
	if (${LLVM_PACKAGE_VERSION} VERSION_LESS "3.8")
		set(llvm_libs LLVM-${LLVM_PACKAGE_VERSION})
	else()
		# only LLVM 3.8+ provide unversioned library
		set(llvm_libs LLVM)
	endif()
else()
	message(STATUS "LLVM linking: static")
	if (NOT ${LLVM_PACKAGE_VERSION} VERSION_LESS "3.4")
		llvm_map_components_to_libnames(llvm_libs support core
		                                irreader bitwriter analysis)
	else()
		llvm_map_components_to_libraries(llvm_libs support core
		                                 irreader bitwriter analysis)
	endif()
endif()

# enable CFG and LLVM in dg
add_definitions(-DENABLE_CFG)
add_definitions(-DHAVE_LLVM)

if(DG_INCLUDE_PATH)
else()
	set(DG_INCLUDE_PATH ${CMAKE_SOURCE_DIR}/dg/include ${CMAKE_SOURCE_DIR}/dg/tools/include)
endif()

if(DG_LIB_PATH)
else()
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

find_library(LIBDGANALYSIS dganalysis PATH ${DG_LIB_PATH})
find_library(LIBPTA dgpta PATH ${DG_LIB_PATH})
find_library(LIBRD dgdda PATH ${DG_LIB_PATH})
find_library(LIBLLVMPTA dgllvmpta PATH ${DG_LIB_PATH})
find_library(LIBLLVMRD dgllvmdda PATH ${DG_LIB_PATH})
find_library(LIBLLVMDG dgllvmdg PATH ${DG_LIB_PATH})
find_library(LIBDGCD dgllvmcda PATH ${DG_LIB_PATH})
find_library(LIBDGTR dgllvmthreadregions PATH ${DG_LIB_PATH})
find_library(LIBDGLLVMSLICER dgllvmslicer PATH ${DG_LIB_PATH}/../tools)

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
	message(STATUS "dgllvmdda library found: ${LIBLLVMRD}")
else()
	message(FATAL_ERROR
	        "dgllvmdda library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()

if (LIBLLVMDG)
	message(STATUS "dgllvmdg library found: ${LIBLLVMDG}")
else()
	message(FATAL_ERROR
	        "dgllvmdg library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()

if (LIBDGCD)
	message(STATUS "libdgllvmcda library found: ${LIBDGCD}")
else()
	message(FATAL_ERROR
	        "libdgllvmcda library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()

if (LIBDGTR)
	message(STATUS "libdgThreadRegions library found: ${LIBDGTR}")
else()
	message(FATAL_ERROR
	        "libdgllvmthreadregions library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()

if (LIBDGLLVMSLICER)
	message(STATUS "libdgllvmslicer library found: ${LIBDGLLVMSLICER}")
else()
	message(FATAL_ERROR
	        "libdgllvmslicer library NOT found! Try specifying -DDG_LIB_PATH=<path>.")
endif()


set(dg_libs ${LIBDGANALYSIS} ${LIBPTA} ${LIBRD}
	    ${LIBLLVMPTA} ${LIBLLVMRD} ${LIBLLVMDG}
	    ${LIBDGCD} ${LIBDGTR} ${LIBDGLLVMSLICER})

include(GNUInstallDirs)
message(STATUS "CMAKE_INSTALL_LIBDIR: \"${CMAKE_INSTALL_LIBDIR}\"")
message(STATUS "CMAKE_INSTALL_DATADIR: \"${CMAKE_INSTALL_FULL_DATADIR}\"")

enable_testing()

add_subdirectory(src)
#add_subdirectory(tests)
