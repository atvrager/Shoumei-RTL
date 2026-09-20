#!/usr/bin/env python3
"""fst_probe.py - ergonomic front-end to the compiled fst_inspect (FST traces).

The raw fst_inspect is a C++ CLI whose signal naming (flat scopes, bit-sliced
buses like `TOP.minstret_e0`..`TOP.minstret_e31`) trips up every user.  This
wrapper:

  * builds `scripts/fst_inspect` on first use (`make tools`) and reports what
    it is doing instead of dumping assembler errors,
  * accepts the trace path or defaults to ./shoumei_cpu.fst,
  * expands bus bases (`minstret`) into their bit members and reassembles one
    hex word per cycle (bit 0 = LSB, the DSL `List.range` convention),
  * routes everything through the machine-readable `--raw` output so scripts
    can parse it directly.

Usage:
  fst_probe.py [trace.fst] list [PATTERN] [--scope S]
  fst_probe.py [trace.fst] dump  SIG[,SIG...] --cycles A-B  [--when SIG=VAL] [--bits]
  fst_probe.py [trace.fst] find  SIG=VAL [--cycles A-B]

  SIG     full/leaf/substring name, or a bus base (`minstret`, `fetch_pc`,
          `rvvi_pc_0`): all `<base>_e<N>` members found in the trace are
          collected and printed as one word per cycle.
  --raw   print the raw `<cycle> <name> <value>` lines, one signal per line.
  --bits  keep bit members expanded instead of reassembling buses into words.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / "scripts" / "fst_inspect"
BIT_RE = re.compile(r"(?:.*\.)?(.*)_e(\d+)$")
IDX_RE = re.compile(r"(?:.*\.)?(.*)_(\d+)$")


def ensure_binary() -> None:
    if BIN.exists():
        return
    print("fst_inspect not built; running `make tools`...", file=sys.stderr)
    r = subprocess.run(["make", "tools"], cwd=ROOT, capture_output=True, text=True)
    if not BIN.exists():
        print(r.stdout, file=sys.stderr)
        print(r.stderr, file=sys.stderr)
        sys.exit("ERROR: could not build scripts/fst_inspect")
    print(f"done: {BIN}", file=sys.stderr)


def run_inspect(trace: Path, args: list[str]) -> str:
    r = subprocess.run(
        [str(BIN), str(trace), *args], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"fst_inspect failed: {r.stderr.strip() or r.stdout.strip()}")
    return r.stdout


def leaf(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def list_signals(trace: Path, scope: str | None) -> list[tuple[int, str]]:
    args = ["--list"]
    if scope:
        args += ["--scope", scope]
    sigs: list[tuple[int, str]] = []
    for line in run_inspect(trace, args).splitlines():
        m = re.match(r"\s*\[\s*(\d+)\]\s+(\S+)", line)
        if m:
            sigs.append((int(m.group(1)), m.group(2)))
    return sigs


def bus_members(trace: Path, base: str) -> list[tuple[str, int]] | None:
    """Bit members of a bus base -> list of (full_name, bit_index), or None."""
    mem_e, mem_i = [], []
    for width, name in list_signals(trace, None):
        if width != 1:
            continue
        m = BIT_RE.match(name)
        if m and m.group(1) == base:
            mem_e.append((name, int(m.group(2))))
            continue
        m = IDX_RE.match(name)
        if m and m.group(1) == base:
            mem_i.append((name, int(m.group(2))))
    for members in (mem_e, mem_i):
        if not members:
            continue
        idxs = sorted(i for _, i in members)
        if idxs == list(range(len(members))):
            return members
    return None


def resolve_sigs(trace: Path, sigs: list[str]) -> list[str]:
    out: list[str] = []
    for s in sigs:
        members = bus_members(trace, s)
        if members:
            out.extend(n for n, _ in sorted(members, key=lambda t: t[1]))
        else:
            out.append(s)
    return out


def fmt_cell(v: str | None, width: int) -> str:
    if v is None:
        return "-" * width
    if v.startswith(("0x", "0X")):
        return v
    return v


def dump(trace: Path, sigs: list[str], cy: str, when: str | None,
         raw: bool, bits: bool) -> None:
    resolved = resolve_sigs(trace, sigs)
    args = ["--raw", "--cycles", cy, "--signals", ",".join(resolved)]
    if when:
        args += ["--when", when]
    out = run_inspect(trace, args)
    if raw:
        sys.stdout.write(out)
        return
    per_cy: dict[int, dict[str, str]] = {}
    for line in out.splitlines():
        p = line.split()
        if len(p) == 3:
            per_cy.setdefault(int(p[0]), {})[p[1]] = p[2]
    # Assign one column per requested signal; buses collapse to their base.
    cols: dict[str, int] = {}
    for name in resolved:
        m = BIT_RE.match(name) if not bits else None
        if m:
            cols.setdefault(m.group(1), len(cols))
        else:
            cols.setdefault(name, len(cols))
    inv = {i: n for n, i in cols.items()}
    hdr = "%6s | " % "cy" + " | ".join("%14s" % inv[i] for i in range(len(cols)))
    print(hdr)
    print("-" * len(hdr))
    for cycle in sorted(per_cy):
        cells = [""] * len(cols)
        for name, val in per_cy[cycle].items():
            m = BIT_RE.match(name) if not bits else None
            if m:
                bit = int(m.group(2))
                n = int(val, 0)
                slot = cols[m.group(1)]
                cells[slot] = str(int(cells[slot] or 0) | (n << bit))
            else:
                cells[cols[name]] = val
        row = "%6d | " % cycle + " | ".join(
            "%14s" % (fmt_cell(c, 14) if c else "-") for c in cells)
        print(row)


def find_cycles(trace: Path, sig: str, val: str, cy: str | None) -> None:
    resolved = resolve_sigs(trace, [sig])
    args = ["--raw", "--signals", ",".join(resolved),
            "--cycles", cy or "0-100000000", "--when", f"{sig}={val}"]
    out = run_inspect(trace, args)
    cycles = sorted({int(line.split()[0]) for line in out.splitlines()
                     if len(line.split()) == 3})
    for c in cycles:
        print(c)


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("trace", nargs="?", default="shoumei_cpu.fst",
                    help="FST trace path (default: ./shoumei_cpu.fst)")
    subs = ap.add_subparsers(dest="cmd", required=True)

    p_list = subs.add_parser("list", help="list signals containing PATTERN")
    p_list.add_argument("pattern", nargs="?", default="")
    p_list.add_argument("--scope")

    p_dump = subs.add_parser("dump", help="dump signal values over a cycle range")
    p_dump.add_argument("sigs", help="comma-separated signal names or bus bases")
    p_dump.add_argument("--cycles", required=True, help="A-B cycle range")
    p_dump.add_argument("--when", help="only cycles where SIG=VAL")
    p_dump.add_argument("--raw", action="store_true", help="raw <cy> <name> <value> lines")
    p_dump.add_argument("--bits", action="store_true", help="keep bit members expanded")

    p_find = subs.add_parser("find", help="print cycles where SIG=VAL")
    p_find.add_argument("sigval", help="SIG=VAL condition")
    p_find.add_argument("--cycles", help="A-B cycle range")

    args = ap.parse_args()
    trace = Path(args.trace)
    if not trace.exists():
        sys.exit(f"ERROR: trace not found: {trace}\n"
                 "  (run `make -C testbench sim-trace` and the sim with +trace)")
    ensure_binary()

    if args.cmd == "list":
        for width, name in list_signals(trace, args.scope):
            hay = name
            if args.pattern and args.pattern not in hay and args.pattern not in leaf(name):
                continue
            print(f"[{width:3}] {name}")
        return 0
    if args.cmd == "dump":
        dump(trace, [s for s in args.sigs.split(",") if s], args.cycles,
             args.when, args.raw, args.bits)
        return 0
    if args.cmd == "find":
        if "=" not in args.sigval:
            sys.exit("ERROR: find expects SIG=VAL")
        sig, val = args.sigval.split("=", 1)
        find_cycles(trace, sig, val, args.cycles)
        return 0
    return 2


if __name__ == "__main__":
    sys.exit(main())