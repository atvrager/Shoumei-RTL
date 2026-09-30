#!/usr/bin/env bash
set -euo pipefail

CPPCHECK="$1"
CFG_FILES="$2"
shift 2

# cppcheck reads its library configuration from the `cfg` directory beside the
# executable, and it resolves that path through the real location of the
# binary.  A symlink therefore does not help: copy the binary next to a link to
# the configuration tree.
CFG_DIR="$(cd "$(dirname "${CFG_FILES%% *}")" && pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp "$CPPCHECK" "$WORK/cppcheck"
ln -s "$CFG_DIR" "$WORK/cfg"
CPPCHECK="$WORK/cppcheck"

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
    "$CPPCHECK" --error-exitcode=1 --enable=warning,style \
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
    "$CPPCHECK" --error-exitcode=1 --enable=warning,style \
        --suppress=missingIncludeSystem \
        --suppress=knownConditionTrueFalse \
        --suppress=syntaxError:testbench/tests/mret_test.c \
        "${c_files[@]}"
fi

echo "PASS: cppcheck clean (${#cpp_files[@]} C++ files, ${#c_files[@]} C files verified)"
