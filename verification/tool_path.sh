#!/usr/bin/env bash
# Put a pinned build tool on PATH.
#
# Usage: source verification/tool_path.sh then run tool_path <tool binary>
#
# The tool's data directory sits next to the binary in the runfiles.  Verilator
# reads its include tree from VERILATOR_ROOT, yosys finds its share tree
# relative to the executable.

tool_path() {
    local tool="$1"
    local root
    root="$(cd "$(dirname "$tool")" && pwd)"

    PATH="$root:$PATH"
    export PATH

    if [[ -e "$root/include/verilated_std.sv" ]]; then
        VERILATOR_ROOT="$root"
        export VERILATOR_ROOT
    fi
}
