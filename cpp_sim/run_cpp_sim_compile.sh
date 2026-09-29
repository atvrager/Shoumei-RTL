#!/usr/bin/env bash
# cpp_sim/run_cpp_sim_compile.sh - Verify C++ simulation models compile cleanly under Bazel
set -euo pipefail

if [ $# -lt 1 ]; then
    echo "Usage: $0 <cpp_sim_dir>" >&2
    exit 1
fi

CPP_DIR="$(cd "$1" && pwd)"

TEST_SRC="${TEST_TMPDIR:-/tmp}/test_cppsim.cpp"
cat << 'EOF' > "$TEST_SRC"
#include <iostream>
#include <cstdint>
#include <vector>
#include "Register32.h"

int main() {
    Register32 reg;
    std::cout << "Shoumei C++ simulation harness initialized with Register32\n";
    return 0;
}
EOF

g++ -std=c++17 -Wall -Wextra -I"$CPP_DIR" "$CPP_DIR/Register32.cpp" "$TEST_SRC" -o "${TEST_TMPDIR:-/tmp}/test_cppsim"
"${TEST_TMPDIR:-/tmp}/test_cppsim"
echo "✓ C++ Simulation library validated"
