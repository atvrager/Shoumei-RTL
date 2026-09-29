#!/usr/bin/env bash
set -euo pipefail

found=0
for f in $(find lean/ -name "*.lean"); do
    matches=$(sed "s/--.*$//" "$f" | grep -w "sorry" || true)
    if [ -n "$matches" ]; then
        echo "Found sorry in $f: $matches"
        found=1
    fi
done

if [ $found -eq 0 ]; then
    echo "PASS: zero sorry proofs found in lean/"
    exit 0
else
    echo "FAIL: incomplete proofs (sorry) found"
    exit 1
fi
