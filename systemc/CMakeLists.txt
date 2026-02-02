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

# Future: Phase 3 will add testbench executables here
# foreach(MODULE_FILE ${SYSTEMC_MODULES})
#   get_filename_component(MODULE_NAME ${MODULE_FILE} NAME_WE)
#   add_executable(${MODULE_NAME}_test
#     ${MODULE_FILE}
#     ../output/systemc/${MODULE_NAME}_tb.cpp
#   )
#   target_link_libraries(${MODULE_NAME}_test SystemC::systemc)
#   target_include_directories(${MODULE_NAME}_test PRIVATE ../output/systemc)
# endforeach()
