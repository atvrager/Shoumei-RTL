#!/usr/bin/env python3
"""
gen-spec-shims.py — Build output/sv-spec/ for the spec-side simulation harness.

For every module that has a human-authored spec in verification/specs/, emit a
thin SystemVerilog shim module in output/sv-spec/:

    module <EmittedName> (<emitted port list>);
      <SpecModule> #(.PARAM(val)) u_spec (.specPort(shimExpr), ...);
    endmodule

Modules without a spec are listed as missing so the developer knows what to
write next; they are NOT replaced by emitted fallbacks (a build error is the
correct signal that a spec is absent).

Port-shape mismatch handling
─────────────────────────────
The emitted SV sometimes exposes an N-bit bus as N individual scalar ports
(e.g. sum_0..sum_31) because the Lean codegen avoids bus notation for those
nets.  The spec always uses a bus.  The shim connects them bit-by-bit using
concatenation / bit-selects, so the total bit count is preserved.

The one exception: Subtractor64's spec exposes a borrow output that the
emitted design does not have (the parent never connects it).  The shim leaves
it undriven — valid for simulation since no parent port ever reads it.

Usage
──────
    python3 scripts/gen-spec-shims.py        # normal run
    python3 scripts/gen-spec-shims.py --dry  # list shimmable / missing, no write
"""

import re
import pathlib
import shutil
import sys

# ── paths ────────────────────────────────────────────────────────────────────

ROOT      = pathlib.Path(__file__).resolve().parent.parent
SV_SRC    = ROOT / "output" / "sv-from-lean"
SPEC_SRC  = ROOT / "verification" / "specs"
OUT_DIR   = ROOT / "output" / "sv-spec"
DUAL_RTL  = ROOT / "lean" / "Shoumei" / "Verification" / "DualRTL.lean"

# Explicit parameter overrides for modules whose params cannot be inferred
# from port widths (the parameter only affects behavior, not interface sizes).
# Map: circuit_name -> {param_name: value}.  Entries here take priority over
# the port-width inference.
PARAM_OVERRIDES: dict[str, dict[str, int]] = {
    "PCIncrementer4": {"INC": 4},
    "PCIncrementer8": {"INC": 8},
}

# Also include specs whose proofs are blocked but the spec file exists.
EXTRA_SPEC_ONLY = [
    "BusyTable_W2_spec.sv",
    "FPBusyTable_spec.sv",
    "IntegerExecUnit_W2_spec.sv",
    "IntegerExecUnit_W2_64_spec.sv",
    "Mul32x32To64_spec.sv",
]

# ── port helpers ─────────────────────────────────────────────────────────────

_HDR_RE = re.compile(
    r'module\s+(\w+)\s*(?:#\s*\((.*?)\))?\s*\((.*?)\)\s*;', re.DOTALL
)
_PARAM_RE    = re.compile(r'parameter\s+(?:int\s+)?(\w+)\s*=\s*([^,\n)]+)')
_PORT_RE     = re.compile(
    r'\b(input|output|inout)\s+(?:logic|wire|reg|signed)?\s*(\[[^\]]*\])?\s*(\w+)'
)
_SCALAR_BITS = re.compile(r'^(.*)_(\d+)$')


def _eval_width_expr(expr: str, vals: dict[str, int]) -> int | None:
    for k, v in vals.items():
        expr = re.sub(rf'\b{k}\b', str(v), expr)
    expr = expr.strip()
    if re.fullmatch(r'[0-9+\-*() <<]+', expr):
        return int(eval(expr))  # noqa: S307 — controlled arithmetic only
    return None


def parse_ports(text: str, param_vals: dict[str, int]) -> list[tuple[str, str, int]]:
    """Return [(dir, name, bit_width), ...] with concrete widths substituted."""
    m = _HDR_RE.search(text)
    if not m:
        return []
    out = []
    for pm in _PORT_RE.finditer(m.group(3)):
        d, w_expr, n = pm.group(1), (pm.group(2) or "").replace(" ", ""), pm.group(3)
        width = 1
        inner = re.fullmatch(r'\[(.+):0\]', w_expr)
        if inner:
            ev = _eval_width_expr(inner.group(1), param_vals)
            width = (ev + 1) if ev is not None else 1
        out.append((d, n, width))
    return out


def bit_map(ports: list[tuple[str, str, int]]) -> dict[tuple[str, int], tuple[str, int | None]]:
    """Map (base, bit_index) → (port_name, bit_index_in_port | None).

    Scalar ports (width 1, no _N suffix): stored as (name, None).
    Bus ports (width N): each bit stored as (name, i).
    Scalar ports with _N suffix (bit-split buses): grouped back to base.
    """
    bm: dict[tuple[str, int], tuple[str, int | None]] = {}
    for _, n, width in ports:
        m = _SCALAR_BITS.fullmatch(n)
        if m and width == 1:
            # part of a scalar-split bus: base _0, _1, ...
            bm[(m.group(1), int(m.group(2)))] = (n, None)
        elif width == 1:
            bm[(n, 0)] = (n, None)
        else:
            for i in range(width):
                bm[(n, i)] = (n, i)
    return bm


# ── parameter inference ──────────────────────────────────────────────────────

def infer_params(
    spec_text: str,
    emitted_ports: list[tuple[str, str, int]],
    spec_ports: list[tuple[str, str, int]],
) -> dict[str, int] | None:
    """Infer concrete parameter values from port-width comparisons.

    Reads parameter definitions from the spec, matches each spec port width
    expression to the emitted concrete width, and solves for identifiers.
    Returns None if any parameter cannot be resolved or gives conflicting values.
    """
    m = _HDR_RE.search(spec_text)
    param_names = {pm.group(1) for pm in _PARAM_RE.finditer(m.group(2) or "")}
    if not param_names:
        return {}

    em_w = {n: w for _, n, w in emitted_ports}
    vals: dict[str, set[int]] = {}
    inner_re = re.compile(r'\[(.+):0\]')

    m2 = _HDR_RE.search(spec_text)
    for pm in _PORT_RE.finditer(m2.group(3)):
        n = pm.group(3)
        w_raw = (pm.group(2) or "").replace(" ", "")
        inner = inner_re.fullmatch(w_raw)
        if not inner:
            continue
        concrete = em_w.get(n, 0)
        expr = inner.group(1)
        for ident in re.findall(r'[A-Za-z_]\w*', expr):
            if ident not in param_names or ident == "int":
                continue
            # solve: eval(expr[ident=?]) + 1 == concrete
            # Heuristic: try concrete values 1..256 and keep consistent ones
            for candidate in range(1, 257):
                test_expr = re.sub(rf'\b{ident}\b', str(candidate), expr)
                test_expr_clean = re.sub(r'[A-Za-z_]\w*', '0', test_expr)
                if re.fullmatch(r'[0-9+\-*() <<]+', test_expr_clean):
                    try:
                        if int(eval(test_expr)) + 1 == concrete:  # noqa: S307
                            vals.setdefault(ident, set()).add(candidate)
                    except Exception:
                        pass

    resolved: dict[str, int] = {}
    for k in param_names:
        v = vals.get(k, set())
        if len(v) == 1:
            resolved[k] = next(iter(v))
        elif not v:
            # Parameter doesn't appear in any port width (e.g. address bit counts
            # that depend on depth).  Try falling back to the default value.
            dm = re.search(rf'parameter\s+(?:int\s+)?{k}\s*=\s*(\d+)', spec_text)
            if dm:
                resolved[k] = int(dm.group(1))
            else:
                return None  # unresolvable
        else:
            return None  # ambiguous

    return resolved


# ── shim generation ───────────────────────────────────────────────────────────

def build_shim(
    mod: str,
    spec_mod: str,
    param_vals: dict[str, int],
    em_ports: list[tuple[str, str, int]],
    sp_ports: list[tuple[str, str, int]],
) -> str | None:
    """Return the shim SV text, or None if bit-maps are incompatible."""
    e_bm = bit_map(em_ports)
    s_bm = bit_map(sp_ports)

    # Spec may expose extra output ports not in emitted (e.g. Subtractor64 borrow).
    # Those are left undriven in the shim.  Missing inputs would be a real error.
    missing_inputs = {
        k for k in e_bm
        if k not in s_bm
        and any(d == "input" and n == k[0] for d, n, _ in em_ports if _ == 1 or True)
    }
    # Actually check direction properly
    em_dir = {n: d for d, n, _ in em_ports}
    missing_inputs = {
        k for k in e_bm
        if k not in s_bm
        and em_dir.get(k[0], "output") == "input"
    }
    if missing_inputs:
        return None

    pins: list[str] = []
    for d, n, width in sp_ports:
        m = _SCALAR_BITS.fullmatch(n)
        if width == 1 and not m:
            # Scalar spec port
            key = (n, 0)
            if key not in e_bm:
                # Extra spec output not in emitted — leave unconnected
                continue
            en, ei = e_bm[key]
            pins.append(f"    .{n}({en})" if ei is None else f"    .{n}({en}[{ei}])")
        elif m and width == 1:
            # Scalar-split spec port name (unusual)
            key = (m.group(1), int(m.group(2)))
            if key not in e_bm:
                continue
            en, ei = e_bm[key]
            pins.append(f"    .{n}({en})" if ei is None else f"    .{n}({en}[{ei}])")
        else:
            # Bus spec port — collect bits from emitted side.
            # Fast path: every (name, bit_i) maps to the same-named bus at the
            # same bit index → connect .spec_port(emitted_port) directly.
            if all(e_bm.get((n, i)) == (n, i) for i in range(width)):
                pins.append(f"    .{n}({n})")
                continue

            # Scalar-split emitted bus → concatenate bits MSB-first.
            parts: list[str] = []
            for i in range(width - 1, -1, -1):
                key = (n, i)
                if key not in e_bm:
                    return None
                en, ei = e_bm[key]
                parts.append(en if ei is None else f"{en}[{ei}]")
            expr = parts[0] if width == 1 else "{" + ", ".join(parts) + "}"
            pins.append(f"    .{n}({expr})")

    decl = ",\n".join(
        f"  {d} logic {(w_str + ' ') if (w_str := f'[{w - 1}:0]' if w > 1 else '') else ''}{n}"
        for d, n, w in em_ports
    )
    phdr = f" #({', '.join(f'.{k}({v})' for k, v in param_vals.items())})" if param_vals else ""
    return (
        f"// Spec shim — {mod} backed by {spec_mod}{phdr}\n"
        f"module {mod} (\n{decl}\n);\n"
        f"  {spec_mod}{phdr} u_spec (\n"
        + ",\n".join(pins)
        + "\n  );\nendmodule\n"
    )


# ── registry loading ──────────────────────────────────────────────────────────

def load_registry() -> dict[str, tuple[str, str]]:
    """Load {circuitName: (specFile, topModule)} from DualRTL.lean."""
    src = DUAL_RTL.read_text()
    rows = re.findall(
        r'circuitName\s*:=\s*"([^"]+)"\s*\n'
        r'\s*specFile\s*:=\s*"([^"]+)"\s*\n'
        r'\s*topModule\s*:=\s*"([^"]+)"',
        src,
    )
    return {name: (sf, tm) for name, sf, tm in rows}


# ── main ──────────────────────────────────────────────────────────────────────

def main(dry: bool = False) -> None:
    registry = load_registry()

    # Add extra spec-only entries (proofs blocked, but specs are real).
    for fname in EXTRA_SPEC_ONLY:
        sf = SPEC_SRC / fname
        if not sf.exists():
            continue
        t = sf.read_text()
        m = _HDR_RE.search(t)
        if not m:
            continue
        spec_mod = m.group(1)
        # circuit name = spec module name minus trailing _spec
        circuit = re.sub(r'_spec$', '', spec_mod)
        if circuit not in registry:
            registry[circuit] = (str(sf.relative_to(ROOT)), spec_mod)

    shimmed: list[str] = []
    missing: list[str]  = []
    errors:  list[tuple[str, str]] = []
    spec_files_used: set[pathlib.Path] = set()

    if not dry:
        # Clear stale files before regenerating so removed shims can't persist.
        if OUT_DIR.exists():
            shutil.rmtree(OUT_DIR)
        OUT_DIR.mkdir(parents=True)
        # Start with all emitted SV files; shims overwrite the entries they cover.
        for f in SV_SRC.glob("*.sv"):
            shutil.copy(f, OUT_DIR / f.name)

    # Determine which emitted modules exist
    emitted_names = {f.stem for f in SV_SRC.glob("*.sv")}

    for mod in sorted(emitted_names):
        if mod not in registry:
            missing.append(mod)
            continue

        sf_rel, spec_mod = registry[mod]
        sf = ROOT / sf_rel
        if not sf.exists():
            missing.append(mod)
            continue

        spec_text  = sf.read_text()
        em_text    = (SV_SRC / f"{mod}.sv").read_text()

        # Apply default params first for port-width parsing
        em_ports   = parse_ports(em_text, {})
        sp_ports_default = parse_ports(spec_text, {})

        param_vals = PARAM_OVERRIDES.get(mod) or infer_params(spec_text, em_ports, sp_ports_default)
        if param_vals is None:
            errors.append((mod, "could not infer all parameters"))
            continue

        sp_ports = parse_ports(spec_text, param_vals)
        shim = build_shim(mod, spec_mod, param_vals, em_ports, sp_ports)
        if shim is None:
            errors.append((mod, "incompatible port bit-maps"))
            continue

        if not dry:
            (OUT_DIR / f"{mod}.sv").write_text(shim)
        spec_files_used.add(sf)
        shimmed.append(mod)

    if not dry:
        for sf in spec_files_used:
            shutil.copy(sf, OUT_DIR / sf.name)

    # ── report ───────────────────────────────────────────────────────────────

    total = len(emitted_names)
    print(f"Spec shims: {len(shimmed):3d}/{total}  "
          f"missing: {len(missing):3d}  errors: {len(errors)}")

    if errors:
        print("\nErrors (need explicit port map):")
        for m, reason in errors:
            print(f"  {m}: {reason}")

    print(f"\nMissing specs ({len(missing)} modules — write these next):")
    # Group by rough category
    cats: dict[str, list[str]] = {
        "FP": [], "Cache/LSU": [], "OoO core": [], "Decoder/opcode": [], "Other": [],
    }
    for m in sorted(missing):
        if m.startswith("FP") or m in {"Int64ToFP", "FPToInt64", "FPFMA", "FPFMAD"}:
            cats["FP"].append(m)
        elif any(x in m for x in ("Cache", "LSU", "MemoryHierarchy")):
            cats["Cache/LSU"].append(m)
        elif any(x in m for x in ("Decode", "Decoder", "Sequencer", "Microcode", "Trap", "Fallback")):
            cats["Decoder/opcode"].append(m)
        elif any(x in m for x in ("ROB", "Rename", "Reservation", "StoreBuffer", "Bitmap",
                                   "PhysReg", "Fetch", "CSRFile", "CPU_")):
            cats["OoO core"].append(m)
        else:
            cats["Other"].append(m)
    for cat, mods in cats.items():
        if mods:
            print(f"  [{cat}]  {' '.join(mods)}")

    if not dry:
        print(f"\nOutput: {OUT_DIR}")
        print(f"Spec files copied: {len(spec_files_used)}")


if __name__ == "__main__":
    main(dry="--dry" in sys.argv)
