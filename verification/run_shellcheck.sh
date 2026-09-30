#!/usr/bin/env bash
set -euo pipefail

SHELLCHECK="$1"
shift

# The pinned shellcheck, not the one on the host.
source verification/tool_path.sh
tool_path "$SHELLCHECK"

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
# -x follows the sources, which live in this repository.
shellcheck -x "${scripts[@]}"
echo "PASS: shellcheck clean (${#scripts[@]} scripts verified)"
