#!/usr/bin/env python3
"""Lint all generated SystemVerilog using slang (IEEE 1800-2017 compliant).

Uses pyslang to parse and elaborate all SV files, reporting any errors
or warnings that Verilator might miss. Catches non-standard constructs,
type mismatches, and elaboration issues.

Usage: python3 verification/slang-lint.py [sv_dir]
"""

import sys
import os
import glob

try:
    import pyslang
except ImportError:
    print("ERROR: pyslang not installed. Run: pip install pyslang")
    sys.exit(1)

sv_dir = sys.argv[1] if len(sys.argv) > 1 else "output/sv-from-lean"

sv_files = sorted(glob.glob(os.path.join(sv_dir, "*.sv")))
if not sv_files:
    print(f"ERROR: No .sv files found in {sv_dir}")
    sys.exit(1)

print(f"slang lint: {len(sv_files)} files in {sv_dir}")

# Parse all files together (so cross-module references resolve)
tree = pyslang.SyntaxTree.fromFiles(sv_files)
compilation = pyslang.Compilation()
compilation.addSyntaxTree(tree)

# Force full elaboration
diagnostics = compilation.getAllDiagnostics()

errors = 0
warnings = 0
for i in range(len(diagnostics)):
    d = diagnostics[i]
    if d.isError():
        errors += 1
    else:
        warnings += 1

if errors > 0 or warnings > 0:
    report = pyslang.DiagnosticEngine.reportAll(
        compilation.sourceManager, diagnostics
    )
    print(report)

print(f"slang lint: {errors} errors, {warnings} warnings")

if errors > 0:
    print("FAIL: slang found errors")
    sys.exit(1)
else:
    print("PASS: all files clean")
    sys.exit(0)
