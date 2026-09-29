#!/usr/bin/env bash
set -euo pipefail

GEN_ARG="$1"
"$GEN_ARG" --check-sec-specs
