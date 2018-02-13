# generate a git-version.h with a HEAD commit hash tag
# (if it changed)
add_custom_target(
	gitversion ALL sh ${CMAKE_CURRENT_SOURCE_DIR}/git-version.sh
)
include_directories(${CMAKE_CURRENT_BINARY_DIR})

add_executable(sbt-slicer sbt-slicer.cpp)
target_link_libraries(sbt-slicer ${dg_libs} ${llvm_libs})
add_dependencies(sbt-slicer gitversion)

install(TARGETS sbt-slicer RUNTIME DESTINATION bin)

