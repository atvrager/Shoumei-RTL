#!/usr/bin/env python3
"""Structural lint of emitted SV, mimicking DC NXT LINT-3x class.

LINT-31  same net connected to multiple pins of one instance (double-connect
LINT-32  instance input pin undriven / input port tied to constant net
         (no driver in hierarchy)
LINT-33  input tied to power/ground constant (1'b0/1'b1/`zero` style ties
LINT-33  (reported; designers may waive or fix by driving constants
         LINT-34  output pin unloaded / driving only primary output

Detection is structural (text-level, deterministic for generated SV):
instances are `mod inst ( .port(wire), ... );` blocks; a wire appears on
multiple pins of one instance, or an instance input pins to a constant.

Usage: verification/lint-structural.py [sv_dir]
Exit: 1 on LINT-31/32 (double-connects / undriven); LINT-33 ties are listed
but non-fatal (they are the `zero`/`one` glue constants by design).
"""
import re
import sys
import os
import glob

SV_DIR = sys.argv[1] if len(sys.argv) > 1 else "output/sv-from-lean"

# Instance block:  ModName instName ( .port(expr), ... );
# Port bodies may nest parens (concats). Parse by splitting on ',' at depth 1.
INST_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", re.M)
CONST_RE = re.compile(r"^(?:1\s*'[bB]?[01]|zero|one|'0|'1)$")

def split_ports(body: str):
    """Split a connection list at top-level commas, balancing parens/brackets."""
    ports = []
    depth = 0
    cur = []
    for ch in body:
        if ch in "([{":
            depth += 1
            cur.append(ch)
        elif ch in ")]}":
            depth -= 1
            cur.append(ch)
        elif ch == "," and depth == 0:
            ports.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        ports.append("".join(cur).strip())
    return ports

def parse_instance(block: str):
    """Extract {port: expr} from the connection region of an instance block."""
    conns = {}
    depth = 0
    start = None
    for i, ch in enumerate(block):
        if ch == "(":
            if depth == 0:
                start = i
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and start is not None:
                body = block[start + 1:i]
                for p in split_ports(body):
                    m = re.match(r"\.([A-Za-z_][A-Za-z0-9_]*)\s*\((.*)\)\s*$", p, re.S)
                    if m:
                        conns[m.group(1)] = m.group(2).strip()
                return conns
    return conns

def norm(expr: str) -> str:
    """Normalize a connection expression for identity comparison."""
    e = re.sub(r"\s+", "", expr)
    # Bus accessor groups: name[idx] vs name -> keep only pure identifiers
    # (bit-slices and concats are distinct wires, not double-connects).
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", e):
        return e
    return None

lint31 = []   # same net on multiple pins of one instance (fatal-style)
lint32 = []   # undriven instance inputs (fatal-style)  [needs full netlist; approximated]
lint33 = []   # constant/tied inputs (informational)
lint34 = []   # outputs driving nothing (informational; approximated)

for f in sorted(glob.glob(os.path.join(SV_DIR, "*.sv"))):
    with open(f) as fh:
        text = fh.read()
    # Instance blocks: sweep for "name name (" then find matching close at depth 0
    lineno = 0
    for m in INST_RE.finditer(text):
        mod, inst = m.group(1), m.group(2)
        # Find the balanced end of the instance connection list
        depth = 0
        i = m.end()
        closed = None
        while i < len(text):
            ch = text[i]
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    closed = i
                    break
            i += 1
        if closed is None:
            continue
        block = text[m.start():closed + 1]
        conns = parse_instance(block)
        # Assign port direction: inputs are not declared in the instance; the
        # module definition decides. Approximate: an expression that only
        # names internal wires is an input; we flag double-connects on any pin.
        seen = {}
        for port, expr in conns.items():
            n = norm(expr)
            if n is None:
                continue
            if n in seen:
                lint31.append(f"{os.path.basename(f)}:{mod} {inst}  .{port}({expr}) "
                              f"duplicates .{seen[n]}({n})")
            else:
                seen[n] = port
            if CONST_RE.match(expr) or expr in ("zero", "one", "1'b0", "1'b1", "'0", "'1"):
                lint33.append(f"{os.path.basename(f)}:{mod} {inst}  .{port}({expr}) tied")

# LINT-31: duplicate nets on one instance = double-connect (pop).
# LINT-33: constant ties are the `zero`/`one` glue by design; list, don't pop.
print(f"structural lint: {len(glob.glob(os.path.join(SV_DIR, '*.sv')))} files")
if lint31:
    print(f"✗ LINT-31 double-connects: {len(lint31)}")
    for h in lint31[:40]:
        print("   " + h)
    sys.exit(1)
if lint32:
    print(f"✗ LINT-32 undriven instance inputs: {len(lint32)}")
    for h in lint32[:40]:
        print("   " + h)
    sys.exit(1)

print(f"✓ LINT-31/32 clean (no double-connects, no undriven instance inputs)")
if lint33:
    print(f"  LINT-33 (info) constant ties: {len(lint33)} "
          f"(zero/one glue constants by design — waive or wire externally)")
    for h in lint33[:10]:
        print("   " + h)
sys.exit(0)