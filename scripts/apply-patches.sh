#!/usr/bin/env bash
# Apply local patches to submodules (idempotent).
# Run from project root or supply PROJ_ROOT.
set -euo pipefail

PROJ_ROOT="${PROJ_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
PATCHES_DIR="$PROJ_ROOT/patches"

apply_one() {
  local submod="$1" patch="$2"
  local submod_dir="$PROJ_ROOT/third_party/$submod"
  local name
  name=$(basename "$patch")

  if [ ! -d "$submod_dir" ]; then
    echo "SKIP  $submod/$name (submodule not checked out)"
    return
  fi

  # Check if already applied (--check exits 0 if patch is already applied)
  if git -C "$submod_dir" apply --check --reverse "$patch" 2>/dev/null; then
    echo "OK    $submod/$name (already applied)"
  else
    git -C "$submod_dir" apply "$patch"
    echo "APPLY $submod/$name"
  fi
}

for submod_dir in "$PATCHES_DIR"/*/; do
  [ -d "$submod_dir" ] || continue
  submod=$(basename "$submod_dir")
  for patch in "$submod_dir"/*.patch; do
    [ -f "$patch" ] || continue
    apply_one "$submod" "$patch"
  done
done
