cmake_minimum_required(VERSION 3.14 FATAL_ERROR)

project(EUForia)
set(EUFORIA_MAJOR 1)
set(EUFORIA_MINOR 0)

# IN_LIST which FindDoxygen needs
cmake_policy(SET CMP0057 NEW)

if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR )
  message (FATAL_ERROR
    "Build outside of the source tree.")
endif()

#--------------------------------------------------------------------------------------------------
# Options:

option(EUFORIA_ENABLE_ASSERTIONS "If false, -DNDEBUG is set" ON)
option(EUFORIA_ENABLE_EXPENSIVE_CHECKS "Enable expensive assertions" OFF)
option(COMPILE_WITH_UBSAN "Compile with clang's UB sanitizer" OFF)
option(COMPILE_WITH_COVERAGE
  "Compile with clang's code coverage instrumentation" OFF)
option(ENABLE_LOGGER "Enable LOG macro" ON)
option(GENERATE_DOXYGEN "Generate doxygen docs of the internals of euforia" OFF)
option(ENABLE_DIRTY_BIT "Enable dirty-bit propagation optimization")
option(ENABLE_GENDATA_FIRST "Enable generalize-data-first optimization")

#--------------------------------------------------------------------------------------------------
# Compiler settings:

# set default build type
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE "Release" CACHE STRING
      "Choose the type of build, options are: Debug Release
RelWithDebInfo MinSizeRel."
      FORCE)
endif(NOT CMAKE_BUILD_TYPE)

# Add path for custom modules
list (APPEND CMAKE_MODULE_PATH
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Default compile flags to yell under a variety of useful conditions.
add_compile_options(-Wall -Wextra -Werror -Wno-unused-function -Wunused-variable
  -Wno-reorder -fno-omit-frame-pointer)
if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "AppleClang")
  add_compile_options( -Weffc++ -Wheader-hygiene -Wold-style-cast -Wshadow)
endif()

# set actual compilation flags based on options
set(CMAKE_CXX_FLAGS_DEBUG "-O0 ${CMAKE_CXX_FLAGS_DEBUG}")
set(CMAKE_CXX_FLAGS_RELEASE "-O3 -march=native ${CMAKE_CXX_FLAGS_RELEASE}")

if (COMPILE_WITH_UBSAN)
  add_compile_options(-fsanitize=undefined -fsanitize-recover=undefined
    -fno-omit-frame-pointer)
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=undefined")
endif()

if (COMPILE_WITH_COVERAGE)
  add_compile_options(-fprofile-instr-generate -fcoverage-mapping)
  message(STATUS "Use LLVM_PROFILE_FILE=file euforia to get profile info")
  if (NOT "${CMAKE_BUILD_TYPE}" STREQUAL "Debug")
    message(WARNING "You are not compiling in Debug mode but you asked for 
    coverage compilation; in all likelihood, you want Debug mode, too")
  endif()
endif()

message(STATUS "Compiler ID is " "${CMAKE_CXX_COMPILER_ID}")

#--------------------------------------------------------------------------------------------------
# Compile flags:

if (EUFORIA_ENABLE_EXPENSIVE_CHECKS)
  add_definitions(-DEXPENSIVECHECKS)
endif()

if (NOT EUFORIA_ENABLE_ASSERTIONS)
  add_definitions(-DNDEBUG)
endif()

if (ENABLE_DIRTY_BIT)
  add_definitions(-DDIRTYBIT)
endif()

if (ENABLE_GENDATA_FIRST)
  add_definitions(-DGENDATA_FIRST)
endif()

if (ENABLE_LOGGER)
  add_definitions(-DLOGGER_ON)
endif()

#--------------------------------------------------------------------------------------------------
# Dependencies:

set(CMAKE_THREAD_PREFER_PTHREAD ON)
include(FindThreads)

# ----------------------------------------
# Z3
find_package(Z3 4.8.7 REQUIRED)
# include_directories(SYSTEM ${Z3_INCLUDE_DIR})

# ----------------------------------------
# Boolector
find_package(Boolector 3.2.1 REQUIRED)


# ----------------------------------------
# Mathsat
if(NOT DEFINED MATHSAT_DIR)
  set(MATHSAT_DIR /opt/mathsat-5.5.1-darwin-libcxx-x86_64/)
endif()
if(EXISTS "${MATHSAT_DIR}" AND IS_DIRECTORY "${MATHSAT_DIR}")
  message(STATUS "Using mathsat at: ${MATHSAT_DIR}")
else()
  message(FATAL_ERROR "MATHSAT_DIR not found: ${MATHSAT_DIR}")
  return()
endif()
include_directories(SYSTEM ${MATHSAT_DIR}/include)
link_directories(${MATHSAT_DIR}/lib)


# ----------------------------------------
# LLVM
# Path to LLVM install
if(NOT DEFINED LLVM_DIR)
  set(LLVM_DIR /opt/llvm-5.0.1/lib/cmake/llvm)
endif()
find_package(LLVM CONFIG NO_DEFAULT_PATH)
if (NOT LLVM_FOUND)
  message(FATAL_ERROR "No llvm found. Please find path/to/cmake/llvm.")
  return()
    #else()
    #set_target_properties(llvm PROPERTIES EXCLUDE_FROM_ALL ON)
endif()
list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
include(AddLLVM)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
#list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
#include(AddLLVM)
#include(HandleLLVMOptions)
#set(LLVM_RUNTIME_OUTPUT_INTDIR ${CMAKE_BINARY_DIR}/${CMAKE_CFG_INTDIR}/bin)
#set(LLVM_LIBRARY_OUTPUT_INTDIR ${CMAKE_BINARY_DIR}/${CMAKE_CFG_INTDIR}/lib)

#set(CMAKE_CXX_FLAGS "${LLVM_CXXFLAGS} ${CMAKE_CXX_FLAGS}")
#set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LLVM_LDFLAGS}")
#set(CMAKE_INSTALL_RPATH "${LLVM_LIBRARY_DIRS};${Z3_DIR}/lib")

include_directories(SYSTEM ${LLVM_INCLUDE_DIRS})
#link_directories(${LLVM_LIBRARY_DIRS})
add_definitions(${LLVM_DEFINITIONS})
#if (NOT DEFINED LLVM_DIR)
#    set(LLVM_DIR /opt/llvm-5.0.0-RTTI)
#endif()

# ----------------------------------------
# Gmp
find_package(Gmp REQUIRED)
if (GMP_FOUND)
  include_directories (${GMP_INCLUDE_DIR})
  include_directories (${GMPXX_INCLUDE_DIR})
else()
  message(FATAL_ERROR "No gmp found")
  return()
  # set(GMP_LIB "")
  # set(GMPXX_LIB "")
endif()

# ----------------------------------------
# Doxygen
if (GENERATE_DOXYGEN)
  set(DOXYGEN_GENERATE_HTML YES)
  # Require dot, treat the other components as optional
  find_package(Doxygen
               REQUIRED dot
               OPTIONAL_COMPONENTS mscgen dia)

             # TODO if this doesn't work can use LIBEUFORIA_SOURCES as input
  if (DOXYGEN_FOUND)
    doxygen_add_docs(doxygen ${CMAKE_SOURCE_DIR})
  endif()
endif()

# ----------------------------------------
# Boost
find_package(Boost
    1.70.0 REQUIRED 
    OPTIONAL_COMPONENTS program_options iostreams)
if (Boost_FOUND)
  include_directories(SYSTEM ${Boost_INCLUDE_DIRS})
  if (Boost_IOSTREAMS_FOUND)
    add_definitions(-DHAVE_BOOST_IOSTREAMS)
  endif()
else()
  message(FATAL_ERROR "Boost 1.70.0 required")
endif()

# ----------------------------------------
# Propagate_const
find_package(propagate_const CONFIG REQUIRED)
# add_subdirectory(${CMAKE_SOURCE_DIR}/lib/jbcoe-propagate_const EXCLUDE_FROM_ALL)

# ----------------------------------------
# Fmtlib
find_package(fmt 5.0.0 CONFIG REQUIRED)
# add_subdirectory(${FMT_DIR} EXCLUDE_FROM_ALL)

#--------------------------------------------------------------------------------------------------
# Build-time generated stuff

# this var will be replaced inside test_euforia.sh
set(EUFORIA_EXAMPLES ${CMAKE_SOURCE_DIR}/../../examples)
configure_file(test_euforia.sh bin/test_euforia.sh @ONLY)
# configure_file(run_euforia.sh.in bin/run_euforia.sh @ONLY)
configure_file(check_sv-comp_unreach.sh bin/euforia_check_sv-comp_unreach.sh
  @ONLY)
configure_file(creduce_euforia.sh bin/creduce_euforia.sh @ONLY)
configure_file(OutputCheckSmt2 bin/OutputCheckSmt2 @ONLY)

#--------------------------------------------------------------------------------------------------
# Tag version with GIT

# The trick to make it always current is to append to
# CMAKE_CONFIGURE_DEPENDS the .git/index file, so that the project is
# re-configured if the Git index file is touched.
# - https://cmake.org/pipermail/cmake/2018-October/068389.html
set_property(DIRECTORY APPEND
    PROPERTY CMAKE_CONFIGURE_DEPENDS
    "${CMAKE_SOURCE_DIR}/../../.git/index")

execute_process(COMMAND git rev-parse HEAD
  OUTPUT_VARIABLE GIT_REV
  ERROR_QUIET)

if ("${GIT_REV}" STREQUAL "")
  set(GIT_REV "NA")
else()
  execute_process(
    COMMAND git rev-parse --abbrev-ref HEAD
    OUTPUT_VARIABLE GIT_BRANCH)
  if ("${GIT_BRANCH}" STREQUAL "")
    set(GIT_BRANCH "NA")
  endif()
  execute_process(
    COMMAND git describe --exact-match --tags
    OUTPUT_VARIABLE GIT_TAG ERROR_QUIET)
  if ("${GIT_TAG}" STREQUAL "")
    set(GIT_TAG "NA")
  endif()
  string(STRIP "${GIT_REV}" GIT_REV)
  string(STRIP "${GIT_TAG}" GIT_TAG)
  string(STRIP "${GIT_BRANCH}" GIT_BRANCH)
endif()

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/src/version.cc.in
    ${CMAKE_CURRENT_BINARY_DIR}/version.cc @ONLY)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/src/git_version.cc.in
  ${CMAKE_CURRENT_BINARY_DIR}/git_version.cc @ONLY)

#--------------------------------------------------------------------------------------------------
# Build targets:

include_directories(src)

set(LIBEUFORIA_SOURCES
    src/supp/euforia_config.cc
    src/supp/debug.cc
    src/supp/wrapstream.cc
    src/supp/expr_latex_fmt.cc
    src/supp/expr_dot_formatter.cc
    src/supp/expr_supp.cc
    src/supp/expr_stats.cc
    src/supp/expr_substitution.cc
    src/supp/expr_set_traversal.cc
    src/supp/solver.cc
    src/supp/z3_solver.cc
    src/supp/boolector_solver.cc
    src/supp/boolector_evaluator.cc
    src/supp/portfolio_solver.cc
    src/supp/std_supp.cc
    src/supp/ip_rep.cc
    src/supp/mathsat_vmt_parser.cc
    src/supp/reachability_graph.cc
    src/supp/boolector_supp.cc
    src/supp/mathsat_supp.cc
    src/supp/model_justifier.cc
    src/supp/nnf_rewriter.cc
    src/supp/expr_flattener.cc
    src/supp/tseitin_rewriter.cc
    src/supp/marco.cc
    src/supp/statistics.cc
    src/xsys/transition_system.cc
    src/xsys/vmt_transition_system.cc
    src/xsys/state_vars.cc
    src/xsys/var_info_traversal.cc
    src/xsys/primary_inputs.cc
    src/xsys/model_pruning_sets.cc
    src/xsys/cyclic_traversal.cc
    src/xsys/influence_traversal.cc
    src/xsys/concrete_vmt_transition_system.cc
    src/xsys/abstract_vmt_transition_system.cc
    src/refinement/layered_refinement.cc
    src/refinement/symex.cc
    src/refinement/state_refiner.cc
    src/refinement/step_refiner.cc
    src/refinement/bmc_symex_refiner.cc
    src/refinement/bmc_one_shot_refiner.cc
    src/refinement/fp_mus_refiner.cc
    src/refinement/rmus.cc
    src/refinement/fp_answer_scrubber.cc
    src/checker_types.cc
    src/cube.cc
    src/tslice.cc
    src/existential_elimination.cc
    src/one_hot.cc
    src/normalize_abstract_expr.cc
    src/abstract_model.cc
    src/abstract_checker.cc
    src/abstract_checker_impl.cc
    src/abstraction_manager.cc
    src/checkersat.cc
    src/checker.cc
    src/counterexample.cc
    ${CMAKE_CURRENT_BINARY_DIR}/git_version.cc
    ${CMAKE_CURRENT_BINARY_DIR}/version.cc
)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
add_custom_target(make-bin-directory ALL COMMAND ${CMAKE_COMMAND}
  -E make_directory ${CMAKE_BINARY_DIR}/bin)

add_library(libeuforia STATIC ${LIBEUFORIA_SOURCES})
set_target_properties(libeuforia PROPERTIES OUTPUT_NAME "euforia")
target_link_libraries(libeuforia PUBLIC z3::libz3 fmt::fmt
  propagate_const::propagate_const)

# Main euforia executable
add_executable(euforia tools/euforia/main.cc)
llvm_map_components_to_libnames(llvm_libs support)
target_link_libraries(euforia
  libeuforia ${llvm_libs} mathsat ${GMPXX_LIB} ${GMP_LIB} z3::libz3
  Boolector::boolector fmt::fmt propagate_const::propagate_const)

if (COMPILE_WITH_COVERAGE)
  target_link_options(euforia BEFORE
    PUBLIC -fprofile-instr-generate -fcoverage-mapping)
endif()

if(${Boost_IOSTREAMS_FOUND})
  target_link_libraries(euforia Boost::iostreams)
endif()

if(${Boost_PROGRAM_OPTIONS_FOUND})
  add_executable(horn2vmt tools/horn2vmt/main.cc)
  target_link_libraries(horn2vmt libeuforia
    Boost::program_options ${llvm_libs} z3::libz3 mathsat ${GMPXX_LIB} ${GMP_LIB}
    Boolector::boolector fmt::fmt)

  add_executable(eufbvabs tools/eufbvabs/main.cc)
  target_link_libraries(eufbvabs libeuforia
    Boost::program_options ${llvm_libs} z3::libz3 mathsat ${GMPXX_LIB} ${GMP_LIB}
    fmt::fmt propagate_const::propagate_const)

  add_executable(z3simp tools/z3simp/main.cc)
  target_link_libraries(z3simp
    Boost::program_options z3::libz3 ${GMPXX_LIB} ${GMP_LIB} fmt::fmt)
else()
    message(WARNING "Not building horn2vmt, eufbvams, z3simp because Boost::program_options not found")
endif()

#SET(CMAKE_SKIP_BUILD_RPATH  FALSE)
#SET(CMAKE_BUILD_WITH_INSTALL_RPATH FALSE)
#SET(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib")
#SET(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)

install(TARGETS euforia
  RUNTIME DESTINATION bin)
# install(PROGRAMS ${CMAKE_BINARY_DIR}/run_euforia.sh
#   DESTINATION bin)

# add_executable(testz3 tests/testz3/main.cc)
# target_link_libraries(testz3 z3 fmt::fmt)
# add_executable(test_model_pruning tests/test_model_pruning/main.cc)
# target_link_libraries(test_model_pruning
#  libeuforia
#  ${BOOLECTOR_LINK_LIBRARIES}
#  ${llvm_libs} z3 mathsat ${GMPXX_LIB} ${GMP_LIB} fmt::fmt)
# add_executable(testboolector tests/testboolector/main.cc)
# target_link_libraries(testboolector
#  libeuforia
#  ${BOOLECTOR_LINK_LIBRARIES}
#  ${llvm_libs} z3 mathsat ${GMPXX_LIB} ${GMP_LIB} fmt::fmt)
# add_executable(testboolectorc tests/testboolectorc/main.cc)
# target_link_libraries(testboolectorc ${BOOLECTOR_LINK_LIBRARIES} Threads::Threads fmt::fmt)
# add_executable(testz3qe tests/testz3qe/main.cc)
# target_link_libraries(testz3qe z3 fmt::fmt)
# if (COMPILE_WITH_COVERAGE)
#   target_link_options(testz3qe BEFORE
#     PUBLIC -fprofile-instr-generate -fcoverage-mapping)
# endif()
# add_executable(testz3arr tests/testz3arr/main.cc)
# target_link_libraries(testz3arr z3 fmt::fmt)
# add_executable(test_graph_traits tests/test_graph_traits/main.cc)
# target_link_libraries(test_graph_traits
#  libeuforia
#  ${BOOLECTOR_LINK_LIBRARIES}
#  ${llvm_libs} z3 mathsat ${GMPXX_LIB} ${GMP_LIB} fmt::fmt)
# add_executable(test_onehot tests/test_onehot/main.cc)
# target_link_libraries(test_onehot
#  libeuforia
#  ${BOOLECTOR_LINK_LIBRARIES}
#  ${llvm_libs} z3 mathsat ${GMPXX_LIB} ${GMP_LIB} fmt::fmt)
# add_executable(testmarco tests/testmarco/main.cc)
# target_link_libraries(testmarco
#  libeuforia
#  ${BOOLECTOR_LINK_LIBRARIES}
#  ${llvm_libs} z3 mathsat ${GMPXX_LIB} ${GMP_LIB} fmt::fmt)
# if (COMPILE_WITH_COVERAGE)
#   target_link_options(test_graph_traits BEFORE
#     PUBLIC -fprofile-instr-generate -fcoverage-mapping)
#   target_link_options(testz3arr BEFORE
#     PUBLIC -fprofile-instr-generate -fcoverage-mapping)
#   target_link_options(test_model_pruning BEFORE
#     PUBLIC -fprofile-instr-generate -fcoverage-mapping)
#   target_link_options(testz3 BEFORE
#     PUBLIC -fprofile-instr-generate -fcoverage-mapping)
# endif()

add_dependencies(euforia make-bin-directory)

add_custom_target(tags
  COMMAND ctags --c++-kinds=+pf --c-kinds=+p --fields=+imaSft --extras=+q -Rnu
  ./src ./tools
  WORKING_DIRECTORY ${CMAKE_SOURCE_DIR})

function(add_clang_static_analysis target)
  get_target_property(SRCs ${target} SOURCES)
  add_library(${target}_analyze OBJECT EXCLUDE_FROM_ALL ${SRCs})
  set_target_properties(${target}_analyze PROPERTIES
    COMPILE_OPTIONS "--analyze;--analyzer-output;html"
    EXCLUDE_FROM_DEFAULT_BUILD true)
endfunction()
add_clang_static_analysis(libeuforia)
add_clang_static_analysis(euforia)

add_subdirectory(test)
