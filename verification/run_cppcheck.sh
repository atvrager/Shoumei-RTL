#!/usr/bin/env bash
set -euo pipefail

cpp_files=()
c_files=()

for f in "$@"; do
    if [ -f "$f" ]; then
        case "$f" in
            *.cpp|testbench/lib/*.h|testbench/riscv-tests/*.h)
                cpp_files+=("$f")
                ;;
            testbench/tests/*.c|testbench/tests/*.h|testbench/coremark/*.c|testbench/coremark/*.h)
                c_files+=("$f")
                ;;
            *.h)
                cpp_files+=("$f")
                ;;
        esac
    fi
done

if [ ${#cpp_files[@]} -gt 0 ]; then
    echo "Checking ${#cpp_files[@]} C++ files with cppcheck..."
    cppcheck --error-exitcode=1 --enable=warning,style \
        --language=c++ \
        --suppress=missingIncludeSystem \
        --suppress=knownConditionTrueFalse \
        --suppress=unusedStructMember \
        --suppress=constParameter \
        --suppress=useStlAlgorithm \
        "${cpp_files[@]}"
fi

if [ ${#c_files[@]} -gt 0 ]; then
    echo "Checking ${#c_files[@]} C files with cppcheck..."
    cppcheck --error-exitcode=1 --enable=warning,style \
        --suppress=missingIncludeSystem \
        --suppress=knownConditionTrueFalse \
        --suppress=syntaxError:testbench/tests/mret_test.c \
        "${c_files[@]}"
fi

echo "PASS: cppcheck clean (${#cpp_files[@]} C++ files, ${#c_files[@]} C files verified)"
