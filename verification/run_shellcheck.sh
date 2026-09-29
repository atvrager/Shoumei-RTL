#!/usr/bin/env bash
set -euo pipefail

scripts=()
for f in "$@"; do
    if [ -f "$f" ]; then
        scripts+=("$f")
    fi
done

if [ ${#scripts[@]} -eq 0 ]; then
    echo "No shell scripts to check."
    exit 0
fi

echo "Checking ${#scripts[@]} shell scripts with shellcheck..."
shellcheck "${scripts[@]}"
echo "PASS: shellcheck clean (${#scripts[@]} scripts verified)"
