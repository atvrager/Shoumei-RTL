#!/usr/bin/env bash
set -euo pipefail

GEN="$1"
"$GEN" --check-lean-root
