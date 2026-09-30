#!/usr/bin/env bash
# run_ty.sh - type check every Python file in the workspace.
set -euo pipefail

TY="$1"

ROOT="${TEST_SRCDIR}/${TEST_WORKSPACE}"
if [ ! -d "$ROOT/verification" ]; then
    ROOT="."
fi

# Without an environment, ty resolves imports against the host python3 and
# its site-packages.  The result then depends on the machine.  An empty
# environment makes every run see the same imports.
ENV_DIR="${TEST_TMPDIR:-$(mktemp -d)}/ty-env"
mkdir -p "$ENV_DIR/lib/python3.12/site-packages"
printf 'home = /nonexistent\nversion_info = 3.12.0\n' > "$ENV_DIR/pyvenv.cfg"

cd "$ROOT"

env -u VIRTUAL_ENV -u CONDA_PREFIX "$TY" check --python "$ENV_DIR" .
