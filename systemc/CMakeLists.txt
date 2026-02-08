cmake_minimum_required(VERSION 3.16)
project(ShoumeiSystemC CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find SystemC installation
# Try pkg-config first, then manual search
find_package(SystemCLanguage CONFIG QUIET)

if(NOT SystemCLanguage_FOUND)
  # Manual SystemC detection (for systems without pkg-config)
  find_path(SYSTEMC_INCLUDE_DIR systemc.h
    PATHS /usr/include /usr/local/include
    PATH_SUFFIXES systemc sysc
  )

  find_library(SYSTEMC_LIBRARY
    NAMES systemc
    PATHS /usr/lib /usr/local/lib /usr/lib/x86_64-linux-gnu /usr/lib/aarch64-linux-gnu
  )

  if(SYSTEMC_INCLUDE_DIR AND SYSTEMC_LIBRARY)
    add_library(SystemC::systemc INTERFACE IMPORTED)
    set_target_properties(SystemC::systemc PROPERTIES
      INTERFACE_INCLUDE_DIRECTORIES "${SYSTEMC_INCLUDE_DIR}"
      INTERFACE_LINK_LIBRARIES "${SYSTEMC_LIBRARY}"
    )
    message(STATUS "Found SystemC: ${SYSTEMC_LIBRARY}")
  else()
    message(FATAL_ERROR "SystemC not found. Install with: yay -S systemc")
  endif()
endif()

# Collect all generated SystemC modules
file(GLOB SYSTEMC_MODULES "../output/systemc/*.cpp")

# Create object library from all modules (validates compilation)
add_library(shoumei_systemc_modules OBJECT ${SYSTEMC_MODULES})
target_link_libraries(shoumei_systemc_modules SystemC::systemc)
target_include_directories(shoumei_systemc_modules PRIVATE ../output/systemc)

# Enable all warnings
target_compile_options(shoumei_systemc_modules PRIVATE
  -Wall -Wextra -Wpedantic
)

# Display modules found
message(STATUS "Found ${CMAKE_MATCH_COUNT} SystemC modules")
message(STATUS "SystemC modules will be compiled as object library")
message(STATUS "Use Phase 3 testbenches to create executables")

# ELF loader library (shared between Verilator and SystemC testbenches)
add_library(elf_loader STATIC ../testbench/lib/elf_loader.cpp)
target_include_directories(elf_loader PUBLIC ../testbench/lib)

# Generated SystemC testbench executables
file(GLOB SC_TESTBENCHES "../testbench/generated/sc_main_*.cpp")
foreach(TB_FILE ${SC_TESTBENCHES})
  get_filename_component(TB_NAME ${TB_FILE} NAME_WE)
  add_executable(${TB_NAME}
    ${TB_FILE}
    $<TARGET_OBJECTS:shoumei_systemc_modules>
  )
  target_link_libraries(${TB_NAME} SystemC::systemc elf_loader)
  target_include_directories(${TB_NAME} PRIVATE ../output/systemc ../testbench/lib)
endforeach()

# Setup files: heavy compilation (includes full module headers) but parallelizable
file(GLOB SC_SETUP_FILES "../testbench/generated/sc_setup_*.cpp")
foreach(SETUP_FILE ${SC_SETUP_FILES})
  get_filename_component(SETUP_NAME ${SETUP_FILE} NAME_WE)
  # Extract module name: sc_setup_FOO -> sc_main_FOO
  string(REPLACE "sc_setup_" "sc_main_" TB_TARGET ${SETUP_NAME})
  if(TARGET ${TB_TARGET})
    target_sources(${TB_TARGET} PRIVATE ${SETUP_FILE})
  endif()
endforeach()
