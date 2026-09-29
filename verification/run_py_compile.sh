#!/usr/bin/env bash
set -euo pipefail

py_files=()
for f in "$@"; do
    if [ -f "$f" ]; then
        py_files+=("$f")
    fi
done

if [ ${#py_files[@]} -eq 0 ]; then
    echo "No Python files to compile."
    exit 0
fi

echo "Checking ${#py_files[@]} Python files with py_compile..."
python3 -m py_compile "${py_files[@]}"
echo "PASS: py_compile clean (${#py_files[@]} files verified)"
