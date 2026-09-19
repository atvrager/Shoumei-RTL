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

args = [a for a in sys.argv[1:] if a != "--sram"]
sv_dir = args[0] if args else "output/sv-from-lean"
sram_mode = "--sram" in sys.argv

if sram_mode:
    # Lint the `ifdef SHOUMEI_SRAM_MACROS` branch (foundry/OpenRAM macros)
    # by defining the macro in every file and adding the behavioral stubs as
    # an extra file.  No text transformation: the preprocessor picks the
    # macro branch naturally, so hierarchy resolves exactly like the default
    # lint (all 168 modules cooperate).
    import tempfile
    stub_path = os.path.join(os.path.dirname(__file__), "sram-macro-stub.sv")
    tmpdir = tempfile.mkdtemp(prefix="slang-sram-")
    sv_files = []
    for f in sorted(glob.glob(os.path.join(sv_dir, "*.sv"))):
        with open(f) as fh:
            content = fh.read()
        tmp = os.path.join(tmpdir, os.path.basename(f))
        with open(tmp, "w") as fh:
            fh.write("`undef SHOUMEI_SRAM_MACROS\n`define SHOUMEI_SRAM_MACROS\n" + content)
        sv_files.append(tmp)
    sv_files.append(os.path.abspath(stub_path))
    print(f"slang lint (SRAM-macros branch): {len(sv_files) - 1} files + macro stubs")
    if len(sv_files) == 1:
        print("  (no SRAM-bearing modules emitted)")
        sys.exit(0)
else:
    sv_files = sorted(glob.glob(os.path.join(sv_dir, "*.sv")))
    print(f"slang lint: {len(sv_files)} files in {sv_dir}")

if not sv_files:
    print(f"ERROR: No .sv files found in {sv_dir}")
    sys.exit(1)

# Parse all files together (so cross-module references resolve)
# Support both older (pyslang <11) and newer (pyslang >=11) module layouts
SyntaxTree = getattr(pyslang, "SyntaxTree", getattr(getattr(pyslang, "syntax", None), "SyntaxTree", None))
Compilation = getattr(pyslang, "Compilation", getattr(getattr(pyslang, "ast", None), "Compilation", None))

tree = SyntaxTree.fromFiles(sv_files)

compilation = Compilation()
compilation.addSyntaxTree(tree)

# Force full elaboration
diagnostics = compilation.getAllDiagnostics()

# Known benign warnings to suppress:
#   - UnconnectedOutputPort: Submodule output ports that the parent module
#     intentionally does not consume (e.g. unused comparator flags, unused RS flags)
SUPPRESSED_CODES = {"UnconnectedOutputPort"}

errors = 0
warnings = 0
active_diagnostics = []
for i in range(len(diagnostics)):
    d = diagnostics[i]
    if d.isError():
        errors += 1
        active_diagnostics.append(d)
    elif str(d.code).split("(")[-1].rstrip(")") not in SUPPRESSED_CODES:
        warnings += 1
        active_diagnostics.append(d)

if errors > 0 or warnings > 0:
    report = pyslang.DiagnosticEngine.reportAll(
        compilation.sourceManager, active_diagnostics
    )
    print(report)

print(f"slang lint: {errors} errors, {warnings} warnings")

if errors > 0 or warnings > 0:
    print("FAIL: slang found errors or warnings")
    sys.exit(1)
else:
    print("PASS: all files clean")
    sys.exit(0)
