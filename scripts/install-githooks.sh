#!/usr/bin/env bash
# install-githooks.sh - install the repo-checked-in git hooks
#
# Copies githooks/* into .git/hooks so fresh checkouts get the same guards.
# Safe to re-run after pulling newer hooks.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
HOOK_SRC="$PROJECT_ROOT/githooks"
HOOK_DST="$(git rev-parse --git-dir)/hooks"

install -m 0755 "$HOOK_SRC"/* "$HOOK_DST/" 2>/dev/null || {
    echo "error: no hooks found in $HOOK_SRC" >&2
    exit 1
}

echo "Installed hooks:"
find "$HOOK_SRC" -maxdepth 1 -type f -printf '  %f\n'