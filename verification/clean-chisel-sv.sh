#!/usr/bin/env bash
# clean-chisel-sv.sh - normalise one Chisel-generated SystemVerilog file so the
# built-in Yosys parser accepts it.
#
# Usage: clean-chisel-sv.sh <output-dir> <input.sv>
#
# The Chisel/CIRCT output carries constructs the built-in parser rejects:
#   1. a trailing "// ----- 8< -----" verification block,
#   2. `automatic logic x = y;` declarations (slang-only),
#   3. stray `automatic` keywords.
set -euo pipefail

out_dir="$1"
f="$2"
bn="$(basename "$f")"

sed '/^\/\/ ----- 8< -----/,$d' "$f" | \
    sed -E 's/([[:space:]])automatic logic\s+([a-zA-Z0-9_]+)\s*=\s*(.+);/\1logic \2;\n\1\2 = \3;/g' | \
    sed 's/[[:space:]]*automatic[[:space:]]+/ /g' > "$out_dir/$bn"
