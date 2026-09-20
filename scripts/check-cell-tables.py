#!/usr/bin/env python3
"""check-cell-tables.py - verify the Lean cell tables against the PDK Liberty.

For every cell in lean/Shoumei/Codegen/CellLibs/*.lean, evaluate the Liberty
`function` of each output pin and the corresponding `CellFunction.model` over
all input assignments.  Any mismatch is a table bug (wrong pin, wrong function,
inverted output) that would otherwise only surface as a silicon-level error.

Usage: scripts/check-cell-tables.py
"""

from __future__ import annotations

import gzip
import itertools
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ASAP7_LIBS = [
    "third_party/orfs/flow/platforms/asap7/lib/NLDM/asap7sc7p5t_SIMPLE_RVT_TT_nldm_211120.lib.gz",
    "third_party/orfs/flow/platforms/asap7/lib/NLDM/asap7sc7p5t_AO_RVT_TT_nldm_211120.lib.gz",
    "third_party/orfs/flow/platforms/asap7/lib/NLDM/asap7sc7p5t_OA_RVT_TT_nldm_211120.lib.gz",
    "third_party/orfs/flow/platforms/asap7/lib/NLDM/asap7sc7p5t_INVBUF_RVT_TT_nldm_220122.lib.gz",
]
GF180_LIB = "third_party/orfs/flow/platforms/gf180/lib/gf180mcu_fd_sc_mcu9t5v0__tt_025C_5v00.lib.gz"

# CellFunction.model, mirrored.
MODEL = {
    "inv":   lambda v: [not v[0]],
    "buf":   lambda v: [v[0]],
    "and2":  lambda v: [v[0] and v[1]],
    "or2":   lambda v: [v[0] or v[1]],
    "xor2":  lambda v: [v[0] != v[1]],
    "nand2": lambda v: [not (v[0] and v[1])],
    "nor2":  lambda v: [not (v[0] or v[1])],
    "mux2":  lambda v: [v[1] if v[2] else v[0]],
    "ao21":  lambda v: [v[2] or (v[0] and v[1])],
    "ao22":  lambda v: [(v[0] and v[1]) or (v[2] and v[3])],
    "aoi21": lambda v: [not (v[2] or (v[0] and v[1]))],
    "aoi22": lambda v: [not ((v[0] and v[1]) or (v[2] and v[3]))],
    "oai21": lambda v: [not ((v[0] or v[1]) and v[2])],
    "fa":    lambda v: [bool(v[0] ^ v[1] ^ v[2]),
                        (v[0] and v[1]) or (v[2] and (v[0] ^ v[1]))],
    "ha":    lambda v: [v[0] != v[1], v[0] and v[1]],
}


def match_brace(txt: str, start: int) -> tuple[int, int] | None:
    i = txt.find("{", start)
    if i < 0:
        return None
    depth = 0
    for j in range(i, len(txt)):
        if txt[j] == "{":
            depth += 1
        elif txt[j] == "}":
            depth -= 1
            if depth == 0:
                return (i, j)
    return None


def load_lib(path: str) -> dict[str, dict[str, str]]:
    """cell -> {output pin -> function}."""
    txt = gzip.open(path, "rt").read()
    out: dict[str, dict[str, str]] = {}
    for m in re.finditer(r"cell\s*\(\s*([^)]+?)\s*\)", txt):
        name = m.group(1)
        b = match_brace(txt, m.end())
        if not b:
            continue
        body = txt[b[0]:b[1]]
        pins: dict[str, str] = {}
        for pm in re.finditer(r"pin\s*\(\s*([^)]+?)\s*\)", body):
            pn = pm.group(1)
            pb = match_brace(body, pm.end())
            if not pb:
                continue
            pbody = body[pb[0]:pb[1]]
            if not re.search(r"direction\s*:\s*output", pbody):
                continue
            f = re.search(r'function\s*:\s*"([^"]*)"', pbody)
            if f:
                pins[pn] = f.group(1)
        out[name] = pins
    return out


# --- Liberty expression evaluation -----------------------------------------

TOKEN = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*|[!*+&|^()'])")


def tokenize(expr: str) -> list[str]:
    toks, pos = [], 0
    while pos < len(expr):
        m = TOKEN.match(expr, pos)
        if not m:
            raise ValueError(f"bad token at {pos} in {expr!r}")
        toks.append(m.group(1))
        pos = m.end()
    return toks


class Parser:
    """Liberty function grammar: OR(+) < XOR(^) < AND(*) < unary(!, postfix ')."""

    def __init__(self, toks: list[str], env: dict[str, bool]):
        self.toks, self.env, self.i = toks, env, 0

    def peek(self) -> str | None:
        return self.toks[self.i] if self.i < len(self.toks) else None

    def eat(self, t: str) -> None:
        if self.peek() != t:
            raise ValueError(f"expected {t!r}, got {self.peek()!r}")
        self.i += 1

    def parse(self) -> bool:
        v = self.or_expr()
        if self.peek() is not None:
            raise ValueError(f"trailing tokens {self.toks[self.i:]}")
        return v

    def or_expr(self) -> bool:
        v = self.xor_expr()
        while self.peek() in ("+", "|"):
            self.i += 1
            rhs = self.xor_expr()
            v = v or rhs
        return v

    def xor_expr(self) -> bool:
        v = self.and_expr()
        while self.peek() == "^":
            self.i += 1
            rhs = self.and_expr()
            v = v != rhs
        return v

    def and_expr(self) -> bool:
        v = self.unary()
        while self.peek() in ("*", "&"):
            self.i += 1
            rhs = self.unary()
            v = v and rhs
        return v

    def unary(self) -> bool:
        if self.peek() == "!":
            self.i += 1
            v = not self.unary()
        elif self.peek() == "(":
            self.i += 1
            v = self.or_expr()
            self.eat(")")
        elif self.peek() == "^":
            raise ValueError("xor needs operands")
        else:
            name = self.peek()
            if name is None or name in ("*", "+", "&", "|", ")", "'"):
                raise ValueError(f"unexpected {name!r}")
            self.i += 1
            v = self.env.get(name)
            if v is None:
                raise ValueError(f"unknown signal {name!r}")
        while self.peek() == "'":
            self.i += 1
            v = not v
        return v


CELL_RE = re.compile(
    r"function\s*:=\s*\.(\w+),\s*svName\s*:=\s*\"([^\"]+)\",\s*"
    r"outputs\s*:=\s*\[([^\]]*)\],\s*inputs\s*:=\s*\[([^\]]*)\]"
)


def lean_cells(path: Path) -> list[tuple[str, str, list[str], list[str]]]:
    out = []
    for fn, sv, outs, ins in CELL_RE.findall(path.read_text()):
        out.append((fn, sv, re.findall(r'"([^"]+)"', outs), re.findall(r'"([^"]+)"', ins)))
    return out


def check(table: Path, lib: dict[str, dict[str, str]], tag: str) -> int:
    bad = 0
    for fn, sv, outs, ins in lean_cells(table):
        pins = lib.get(sv)
        if pins is None:
            print(f"FAIL {tag} {sv}: cell not found in Liberty")
            bad += 1
            continue
        for out_pin in outs:
            expr = pins.get(out_pin)
            if expr is None:
                print(f"FAIL {tag} {sv}: no function for output pin {out_pin}")
                bad += 1
                continue
            n = len(ins)
            for bits in itertools.product([False, True], repeat=n):
                env = dict(zip(ins, bits))
                try:
                    lib_val = Parser(tokenize(expr), env).parse()
                except ValueError as exc:
                    print(f"FAIL {tag} {sv}.{out_pin}: cannot parse {expr!r}: {exc}")
                    bad += 1
                    break
                model_val = MODEL[fn](bits)[outs.index(out_pin)]
                if lib_val != model_val:
                    print(f"FAIL {tag} {sv}.{out_pin} {fn}{ins}={bits}: "
                          f"liberty={lib_val} model={model_val} ({expr})")
                    bad += 1
                    break
    print(f"{tag}: {'OK' if bad == 0 else str(bad) + ' mismatches'}")
    return bad


def main() -> int:
    asap7: dict[str, dict[str, str]] = {}
    for p in ASAP7_LIBS:
        asap7.update(load_lib(str(ROOT / p)))
    gf180 = load_lib(str(ROOT / GF180_LIB))
    bad = check(ROOT / "lean/Shoumei/Codegen/CellLibs/ASAP7.lean", asap7, "ASAP7")
    bad += check(ROOT / "lean/Shoumei/Codegen/CellLibs/GF180.lean", gf180, "GF180")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
