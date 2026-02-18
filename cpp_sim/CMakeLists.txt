cmake_minimum_required(VERSION 3.16)
project(ShoumeiCppSim CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Collect all generated C++ simulation modules
file(GLOB CPPSIM_MODULES "../output/cpp_sim/*.cpp")

# Create object library from all modules (validates compilation)
add_library(shoumei_cppsim_modules OBJECT ${CPPSIM_MODULES})
target_include_directories(shoumei_cppsim_modules PRIVATE ../output/cpp_sim)

# Enable all warnings
target_compile_options(shoumei_cppsim_modules PRIVATE
  -Wall -Wextra -Wpedantic -O2
)

# Display modules found
message(STATUS "C++ simulation modules will be compiled as object library")

# ELF loader library (shared between Verilator and C++ simulation testbenches)
add_library(elf_loader STATIC ../testbench/lib/elf_loader.cpp)
target_include_directories(elf_loader PUBLIC ../testbench/lib)

# Generated C++ simulation testbench executables
file(GLOB SIM_TESTBENCHES "../testbench/generated/sim_main_CPU_*.cpp")
foreach(TB_FILE ${SIM_TESTBENCHES})
  get_filename_component(TB_NAME ${TB_FILE} NAME_WE)
  add_executable(${TB_NAME}
    ${TB_FILE}
    $<TARGET_OBJECTS:shoumei_cppsim_modules>
  )
  target_link_libraries(${TB_NAME} elf_loader)
  target_include_directories(${TB_NAME} PRIVATE ../output/cpp_sim ../testbench/lib ../testbench/generated)
endforeach()

# Setup files: heavy compilation (includes full module headers) but parallelizable
file(GLOB CPU_SETUP_FILES "../testbench/generated/cpu_setup_*.cpp")
foreach(SETUP_FILE ${CPU_SETUP_FILES})
  get_filename_component(SETUP_NAME ${SETUP_FILE} NAME_WE)
  # Extract module name: cpu_setup_FOO -> sim_main_FOO
  string(REPLACE "cpu_setup_" "sim_main_" TB_TARGET ${SETUP_NAME})
  if(TARGET ${TB_TARGET})
    target_sources(${TB_TARGET} PRIVATE ${SETUP_FILE})
  endif()
endforeach()
