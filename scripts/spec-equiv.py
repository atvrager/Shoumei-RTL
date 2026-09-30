#!/usr/bin/env python3
"""
spec-equiv.py — randomised differential co-simulation of the emitted RTL against
its hand-written spec, module by module.

For one module this writes a self-checking SystemVerilog testbench that
instantiates the emitted netlist and the spec side by side, drives every input
from an LFSR, and compares every output each cycle.  It copies the testbench,
the spec, and the netlist sources into one output directory.  The
`spec_equiv_test` macro (verification/spec_equiv.bzl) runs this script in a
build action, compiles the directory with rules_verilator, and runs the model
as a test.  The testbench stops with $fatal on the first run with a mismatch.

This is the equivalence check for modules where the SMT route does not scale
(wide state, wide interfaces), and for the spec-side simulation harness: a spec
that lags the RTL by one cycle is invisible to a functional test suite but
visible here.

Usage
─────
    bazel test //verification:spec_equiv_test
"""

import argparse
import importlib.util
import os
import pathlib
import re
import shutil
import sys
import types

ROOT = (
    pathlib.Path().resolve()
    if pathlib.Path("verification/specs").exists()
    else pathlib.Path(__file__).resolve().parent.parent
)
SV_SRC = ROOT / "output" / "sv-from-lean"
SPEC_SRC = ROOT / "verification" / "specs"
DUAL_RTL = ROOT / "lean" / "Shoumei" / "Verification" / "DualRTL.lean"

# Specs that are real but whose SEC proof is not registered yet.
EXTRA_SPEC_ONLY = [
    "BusyTable_W2",
    "FPBusyTable",
    "IntegerExecUnit_W2",
    "IntegerExecUnit_W2_64",
    "Mul32x32To64",
]

LFSR_BITS = 1024
CLOCK_NAMES = ("clock", "clk")
RESET_NAMES = ("reset", "rst", "rst_n", "resetn")

_HDR_RE = re.compile(r"module\s+(\w+)\s*(?:#\s*\((.*?)\))?\s*\((.*?)\)\s*;", re.DOTALL)
_PORT_RE = re.compile(
    r"\b(input|output|inout)\s+(?:logic|wire|reg|signed)?\s*(\[[^\]]*\])?\s*(\w+)"
)


def _width(expr: str, vals: dict[str, int]) -> int:
    for k, v in vals.items():
        expr = re.sub(rf"\b{k}\b", str(v), expr)
    if re.fullmatch(r"[0-9+\-*() <<]+", expr):
        return int(eval(expr)) + 1
    return 1


def ports_of(text: str, vals: dict[str, int] | None = None) -> list[tuple[str, str, int]]:
    """[(direction, name, width_in_bits), ...] in declaration order."""
    m = _HDR_RE.search(text)
    if not m:
        return []
    out = []
    for pm in _PORT_RE.finditer(m.group(3)):
        d, w, n = pm.group(1), (pm.group(2) or "").replace(" ", ""), pm.group(3)
        inner = re.fullmatch(r"\[(.+):0\]", w)
        out.append((d, n, _width(inner.group(1), vals or {}) if inner else 1))
    return out


def infer_params(
    spec_text: str,
    em_ports: list[tuple[str, str, int]],
    _sp_ports: list[tuple[str, str, int]],
) -> dict[str, int] | None:
    """Recover concrete parameter values by matching spec widths to emitted ones."""
    m = _HDR_RE.search(spec_text)
    assert m is not None
    params = {
        pm.group(1) for pm in re.finditer(r"parameter\s+(?:int\s+)?(\w+)\s*=", m.group(2) or "")
    }
    if not params:
        return {}

    em_w = {n: w for _, n, w in em_ports}
    vals: dict[str, set[int]] = {}
    for pm in _PORT_RE.finditer(m.group(3)):
        n = pm.group(3)
        inner = re.fullmatch(r"\[(.+):0\]", (pm.group(2) or "").replace(" ", ""))
        if not inner:
            continue
        concrete = em_w.get(n, 0)
        for ident in re.findall(r"[A-Za-z_]\w*", inner.group(1)):
            if ident not in params:
                continue
            for cand in range(1, 2049):
                e = re.sub(rf"\b{ident}\b", str(cand), inner.group(1))
                if not re.fullmatch(r"[0-9+\-*() <<]+", re.sub(r"[A-Za-z_]\w*", "0", e)):
                    continue
                try:
                    if int(eval(e)) + 1 == concrete:
                        vals.setdefault(ident, set()).add(cand)
                except Exception:
                    pass

    out: dict[str, int] = {}
    for k in sorted(params):
        v = vals.get(k, set())
        if len(v) == 1:
            out[k] = next(iter(v))
        elif v:
            return None  # ambiguous
        else:
            dm = re.search(rf"parameter\s+(?:int\s+)?{k}\s*=\s*(\d+)", spec_text)
            if not dm:
                return None
            out[k] = int(dm.group(1))
    return out


def load_registry() -> dict[str, tuple[str, str]]:
    src = DUAL_RTL.read_text()
    rows = re.findall(
        r'circuitName\s*:=\s*"([^"]+)"\s*\n'
        r'\s*specFile\s*:=\s*"([^"]+)"\s*\n'
        r'\s*topModule\s*:=\s*"([^"]+)"',
        src,
    )
    reg = {n: (sf, tm) for n, sf, tm in rows}
    for mod in EXTRA_SPEC_ONLY:
        sf = SPEC_SRC / f"{mod}_spec.sv"
        if sf.exists() and mod not in reg:
            m = _HDR_RE.search(sf.read_text())
            if m:
                reg[mod] = (str(sf.relative_to(ROOT)), m.group(1))
    return reg


_GB: types.ModuleType | None = None
_GS: types.ModuleType | None = None


def _gs() -> types.ModuleType:
    """gen-spec-shims.py: one owner for the bit-level port mapping and the
    parameter overrides that port widths cannot express."""
    global _GS
    if _GS is None:
        spec = importlib.util.spec_from_file_location("gs", ROOT / "scripts" / "gen-spec-shims.py")
        assert spec is not None and spec.loader is not None
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _GS = mod
    return _GS


def _gb() -> types.ModuleType:
    """gen-bridges.py, loaded once per process (its import is not free).

    Assigns `_GB` only after `exec_module` returns: workers run in threads, and
    publishing the module early makes a concurrent reader see a half-built one."""
    global _GB
    if _GB is None:
        spec = importlib.util.spec_from_file_location("gb", ROOT / "scripts" / "gen-bridges.py")
        assert spec is not None and spec.loader is not None
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _GB = mod
    return _GB


def deps_of(mod: str) -> list[str]:
    """Emitted-netlist dependencies, plus any spec the spec itself instantiates."""
    gb = _gb()
    gb.__dict__["SV_DIR"] = SV_SRC
    return gb.sv_deps(mod).split() + [str(SPEC_SRC / d) for d in gb.SPEC_DEPS.get(mod, [])]


def make_tb(
    mod: str,
    dut_ports: list[tuple[str, str, int]],
    spec_mod: str,
    params: dict,
    cycles: int,
    ref_pins: list[str],
) -> str:
    clk_name = next((n for d, n, _ in dut_ports if d == "input" and n in CLOCK_NAMES), None)
    rst_name = next((n for d, n, _ in dut_ports if d == "input" and n in RESET_NAMES), None)
    stim = [(n, w) for d, n, w in dut_ports if d == "input" and n not in (clk_name, rst_name)]
    outs = [(n, w) for d, n, w in dut_ports if d == "output"]

    L: list[str] = [
        f"// Generated by spec-equiv.py — differential co-simulation of {mod}",
        f"module tb_{mod};",
        "  logic clock = 1'b0;",
    ]
    if rst_name:
        L.append(f"  logic {rst_name} = 1'b1;")
    for n, w in stim:
        L.append(f"  logic [{w - 1}:0] {n};")
    for n, w in outs:
        L.append(f"  logic [{w - 1}:0] dut_{n}, ref_{n};")

    def connections(prefix: str) -> str:
        p = []
        for d, n, _ in dut_ports:
            if n == clk_name:
                p.append(f"    .{n}(clock)")
            elif n == rst_name:
                p.append(f"    .{n}({rst_name})")
            elif d == "output":
                p.append(f"    .{n}({prefix}_{n})")
            else:
                p.append(f"    .{n}({n})")
        return ",\n".join(p)

    phdr = f" #({', '.join(f'.{k}({v})' for k, v in params.items())})" if params else ""
    L += [
        f"  {mod} u_dut (\n{connections('dut')}\n  );",
        f"  {spec_mod}{phdr} u_ref (\n" + ",\n".join(ref_pins) + "\n  );",
        "",
        "  always #5 clock = ~clock;",
        f"  logic [{LFSR_BITS - 1}:0] lfsr = {LFSR_BITS}'h0123456789ABCDEF0BADF00D5A5A5A5A;",
        f"  always @(posedge clock) lfsr <= {{lfsr[{LFSR_BITS - 2}:0], lfsr[{LFSR_BITS - 1}]^lfsr[{LFSR_BITS - 2}]^lfsr[{LFSR_BITS - 3}]}};",
        "",
    ]

    # stimulus: each input gets its own slice of the LFSR, all moving together
    L.append("  initial begin")
    L.append("    " + "; ".join(f"{n} = 0" for n, _ in stim) + ";")
    if rst_name:
        L += [
            f"    {rst_name} = 1'b1;",
            "    repeat (3) @(posedge clock);",
            f"    {rst_name} = 1'b0;",
        ]
    L.append("    forever begin")
    L.append("      @(negedge clock);")
    for i, (n, w) in enumerate(stim):
        off = (i * 5) % max(1, LFSR_BITS - w)
        L.append(f"      {n} = lfsr[{off} +: {w}];")
    L += ["    end", "  end", ""]

    if outs:
        cmp = " || ".join(f"dut_{n} !== ref_{n}" for n, _ in outs)
        fmt = " ".join(f"{n}=%h/%h" for n, _ in outs)
        args = ", ".join(f"dut_{n}, ref_{n}" for n, _ in outs)
        L += [
            "  int errors = 0, cycles = 0;",
            "  always @(posedge clock) begin",
            "    cycles <= cycles + 1;",
        ]
        guard = f"!{rst_name} && " if rst_name else ""
        L += [
            f"    if ({guard}cycles > 3)",
            f"      if ({cmp}) begin",
            "        errors <= errors + 1;",
            f'        if (errors < 4) $display("MISMATCH cyc=%0d {fmt}", cycles, {args});',
            "      end",
            "  end",
            "",
            "  initial begin",
            f"    repeat ({cycles}) @(posedge clock);",
            '    $display("cycles=%0d errors=%0d", cycles, errors);',
            '    if (errors != 0) $fatal(1, "emitted RTL and spec differ");',
            "    $finish;",
            "  end",
        ]
    else:
        L += [
            "  initial begin",
            f"    repeat ({cycles}) @(posedge clock);",
            '    $display("cycles=%0d errors=0", ' + str(cycles) + ");",
            "    $finish;",
            "  end",
        ]
    L.append("endmodule")
    return "\n".join(L) + "\n"


def emit(mod: str, reg: dict[str, tuple[str, str]], cycles: int, out: pathlib.Path) -> str | None:
    """Write the testbench and copy its sources into `out`.  Return an error
    message, or None on success."""
    if mod not in reg:
        return "no spec"
    sf_rel, spec_mod = reg[mod]
    sf, ef = ROOT / sf_rel, SV_SRC / f"{mod}.sv"
    if not sf.exists() or not ef.exists():
        return "missing file"

    em_ports = ports_of(ef.read_text())
    spec_text = sf.read_text()
    params = _gs().PARAM_OVERRIDES.get(mod) or infer_params(
        spec_text, em_ports, ports_of(spec_text, {})
    )
    if params is None:
        return "param inference failed"

    # Port connection uses the same bit-level mapping as the shim generator:
    # the emitted netlist exposes some buses as scalar ports (sum_0..sum_N).
    ref_ports = ports_of(spec_text, params)
    pins = _gs().spec_pins(spec_mod, params, em_ports, ref_ports)
    if pins is None:
        return "port sets incompatible"

    # spec_pins names the emitted ports; the testbench publishes ref outputs as
    # ref_<name>.  Rewrite only the expression inside each pin — the pin name is
    # the spec's port name and must not be touched.
    ref_pins = []
    outs_map = [(n, f"ref_{n}") for d, n, _ in em_ports if d == "output"]
    for pin in pins:
        head, _, expr = pin.partition("(")
        for name, repl in outs_map:
            expr = re.sub(rf"\b{re.escape(name)}\b", repl, expr)
        ref_pins.append(f"{head}({expr}")

    out.mkdir(parents=True, exist_ok=True)
    (out / f"tb_{mod}.sv").write_text(make_tb(mod, em_ports, spec_mod, params, cycles, ref_pins))
    for src in [str(sf), *deps_of(mod)]:
        shutil.copyfile(src, out / pathlib.Path(src).name)
    return None


def main() -> int:
    global SV_SRC
    ap = argparse.ArgumentParser()
    ap.add_argument("module")
    ap.add_argument("--cycles", type=int, required=True)
    ap.add_argument("--sv-dir", type=pathlib.Path, required=True, help="emitted SV directory")
    ap.add_argument("--out", type=pathlib.Path, required=True, help="output directory")
    args = ap.parse_args()

    SV_SRC = args.sv_dir.resolve()
    os.environ["SV_DIR"] = str(SV_SRC)

    err = emit(args.module, load_registry(), args.cycles, args.out)
    if err:
        print(f"spec-equiv: {args.module}: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
