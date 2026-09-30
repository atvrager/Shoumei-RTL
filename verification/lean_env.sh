#!/usr/bin/env bash
# lean_env.sh - the Lean compiler and the library oleans of a test.
#
# A test that compiles Lean at run time takes the compiler from the toolchain
# (an argument of the test) and the library oleans from its own runfiles.
# Nothing is read from the host.
#
# Usage: . lean_env.sh then lean_env <lean binary> <runfiles root>.
# LIB_LEAN_PATH then holds the directory that satisfies `import Shoumei.Foo`.

lean_env() {
    local lean_bin="$1"
    local root="$2"

    local lean_dir
    lean_dir="$(cd "$(dirname "$lean_bin")" && pwd)"
    export PATH="$lean_dir:${PATH}"

    local olean
    olean="$(find "$root" -name DSL.olean -print -quit 2>/dev/null || true)"
    if [ -z "$olean" ]; then
        echo "lean_env: the runfiles hold no library oleans" >&2
        return 1
    fi

    # The path is <olean dir>/Shoumei/DSL.olean, so the search path is two
    # directories up.
    local olean_dir
    olean_dir="$(dirname "$(dirname "$olean")")"
    export LIB_LEAN_PATH="$olean_dir"
}
