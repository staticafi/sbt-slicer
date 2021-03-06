# --------------------------------------------------
# Generate a git-version.h with a HEAD commit hash
# --------------------------------------------------
find_package(Git)
if(NOT Git_FOUND OR NOT EXISTS ${CMAKE_SOURCE_DIR}/.git AND NOT GIT_VERSION)
  set(GIT_VERSION "unknown")
else()
  execute_process(COMMAND ${GIT_EXECUTABLE} rev-parse --short=8 HEAD
                  OUTPUT_STRIP_TRAILING_WHITESPACE
                  OUTPUT_VARIABLE NEW_GIT_VERSION)
  if(NOT "${GIT_VERSION}" STREQUAL "${NEW_GIT_VERSION}")
      set(GIT_VERSION ${NEW_GIT_VERSION})
  endif()
endif()

set(GIT_VERSION ${GIT_VERSION} CACHE STRING "Git version hash" FORCE)
configure_file(git-version.h.in git-version.h @ONLY)
include_directories(${CMAKE_CURRENT_BINARY_DIR})

# --------------------------------------------------
# sbt-slicer
# --------------------------------------------------
add_executable(sbt-slicer sbt-slicer.cpp)
target_link_libraries(sbt-slicer ${DG_LIBS} ${LLVM_LIBS})

install(TARGETS sbt-slicer RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
