#!/usr/bin/env python3
"""gen-project-map.py - generate docs/project-map.md from the source itself.

The map is *derived*, not hand-written, so it cannot rot: re-run it after adding
a module and the composition graph, the coverage table and the mechanical gap
list all update.

Sources (all tracked - the map must be reproducible in a fresh checkout, since
`lint` asserts it is current):
  lean/**/*.lean                                  circuit literals, doc comments, instances
  lean/Shoumei/Verification/CompositionalCerts.lean  compositional certificates
  GenerateAll.lean                                the canonical circuit registry

Usage:  scripts/gen-project-map.py [--out docs/project-map.md]
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
# Certs come from the Lean registry rather than the exported text file: the
# export is untracked and generated, so reading it would make the map depend on
# whether codegen has run.
CERT_REGISTRY = LEAN / "Shoumei" / "Verification" / "CompositionalCerts.lean"
REFINEMENT_REGISTRY = LEAN / "Shoumei" / "Verification" / "Refinements.lean"
GENERATE_ALL = ROOT / "GenerateAll.lean"

RE_INSTANCE = re.compile(r'moduleName\s*:=\s*"([A-Za-z0-9_]+)"')
# A Circuit literal: `{ name := "X"` directly followed by its `inputs :=` field.
# The `inputs` requirement is what separates a circuit from the hundreds of
# signal-group records (`{ name := "dispatch_base", width := 32 }`) in the same
# files.  Circuits whose name is built by interpolation (`s!"Foo_{n}"`) cannot be
# located this way; main() notes that limit rather than guessing.
RE_CIRCUIT_NAME = re.compile(
    r'\{\s*name\s*:=\s*"([A-Za-z0-9_]+)"\s*,?\s*inputs\s*:=', re.M
)
RE_DEF = re.compile(r"^def\s+(mk[A-Za-z0-9_]*)\b", re.M)
RE_HEADER = re.compile(r"^/\-(.*?)-/", re.S | re.M)

# Hand-maintained: knowledge that is not extractable from the tree.  Keep short.
KNOWN_GAPS = [
    "The `Circuit satisfies Behavior` atom exists (`Verification/Implements.lean`) "
    "and composes (`implements_compose`), but coverage is partial -- see the "
    "Refines column.  No RISC-V module carries one yet.",
    "Certificates are unverified pointers: `CompositionalCert.proofReference` is "
    "a `String` and the LEC script only checks that dependencies were verified.",
    "Widths are fixed to 64-bit for the RV64G core: `CPUConfig.xlen = 64` and "
    "`CPUConfig.flen = 64`. Parameterized width polymorphism across 32/64-bit "
    "is not yet abstracted into a single unified top-level circuit generator.",
    "The flat netlist emitter (`SystemVerilogNetlist.lean`) is "
    "combinational-only: it drops DFFs and clock/reset, and full instance "
    "inlining does not scale (8.7 MB for one module).",
    "The CPU top-level has no compositional certificate, so it is the dominant "
    "cost of a full LEC run.",
]


def first_doc_header(text: str) -> str | None:
    """Return the first module doc comment, as a single line."""
    m = RE_HEADER.search(text)
    if not m:
        return None
    body = m.group(1)
    for line in body.splitlines():
        s = line.strip().lstrip("*").strip()
        if s:
            return s
    return None


def load_certs() -> dict[str, list[str]]:
    """moduleName -> dependencies, read from the Lean certificate registry."""
    certs: dict[str, list[str]] = {}
    if not CERT_REGISTRY.exists():
        return certs
    text = CERT_REGISTRY.read_text()
    for rec in text.split("CompositionalCert := {")[1:]:
        body = rec.split("}")[0]
        m = re.search(r'moduleName\s*:=\s*"([A-Za-z0-9_]+)"', body)
        if not m:
            continue
        deps = re.search(r'dependencies\s*:=\s*\[(.*?)\]', body, re.S)
        names = re.findall(r'"([A-Za-z0-9_]+)"', deps.group(1)) if deps else []
        certs[m.group(1)] = names
    return certs


def load_refinements() -> dict[str, str]:
    """moduleName -> specName, read from the Lean refinement registry."""
    refinements: dict[str, str] = {}
    if not REFINEMENT_REGISTRY.exists():
        return refinements
    text = REFINEMENT_REGISTRY.read_text()
    for m in re.finditer(
        r'\.(?:combinational|sequential)\s+"([A-Za-z0-9_]+)"\s+"([A-Za-z0-9_]+)"',
        text,
    ):
        refinements[m.group(1)] = m.group(2)
    return refinements


def registry_order() -> list[str]:
    """Circuit names in GenerateAll order (best-effort)."""
    if not GENERATE_ALL.exists():
        return []
    return sorted(set(re.findall(r"\b(mk[A-Za-z0-9_]+)\b", GENERATE_ALL.read_text())))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="docs/project-map.md")
    args = ap.parse_args()

    lean_files = sorted(LEAN.rglob("*.lean"))
    if not lean_files:
        print("no Lean sources found", file=sys.stderr)
        return 1

    # name -> defining file, doc comment, defs, instances
    circuit_file: dict[str, Path] = {}
    file_text: dict[Path, str] = {}

    for f in lean_files:
        text = f.read_text(errors="replace")
        file_text[f] = text
        for name in RE_CIRCUIT_NAME.findall(text):
            circuit_file.setdefault(name, f)

    defs_by_file = {f: RE_DEF.findall(t) for f, t in file_text.items()}
    inst_by_file = {f: set(RE_INSTANCE.findall(t)) for f, t in file_text.items()}

    known = set(circuit_file)
    certs = load_certs()
    refinements = load_refinements()

    # Composition edges, restricted to real circuits.
    edges: dict[str, set[str]] = {}
    for name, f in circuit_file.items():
        children = inst_by_file[f] & known
        children.discard(name)
        edges[name] = children

    def subsystem(f: Path) -> str:
        parts = f.relative_to(LEAN).parts
        return "/".join(parts[:-1]) if len(parts) > 1 else "(root)"

    subsys_of = {n: subsystem(f) for n, f in circuit_file.items()}

    # Subsystem-level graph: cross-subsystem edges, with counts.
    cross: dict[tuple[str, str], int] = defaultdict(int)
    for parent, kids in edges.items():
        for kid in kids:
            a, b = subsys_of[parent], subsys_of[kid]
            if a != b:
                cross[(a, b)] += 1

    by_subsys: dict[str, list[str]] = defaultdict(list)
    for n in circuit_file:
        by_subsys[subsys_of[n]].append(n)

    # Proofs are looked for across the whole tree, not one directory: a circuit
    # is often proven in a sibling Proofs file in a different subsystem.
    proven_names: set[str] = set()
    for pf in LEAN.rglob("*Proofs.lean"):
        text = pf.read_text(errors="replace")
        for n in known:
            if n in text:
                proven_names.add(n)

    def has_proofs(name: str) -> bool:
        return name in proven_names

    out: list[str] = []
    out.append("# Project Map")
    out.append("")
    out.append("Generated by `scripts/gen-project-map.py` from the source tree — do")
    out.append("not edit by hand; re-run it.  Composition edges come from")
    out.append("`moduleName :=` references between circuits, certificates from the")
    out.append("Lean registry, docs from each file's leading comment block.")
    out.append("")
    out.append(f"- Lean files: **{len(lean_files)}**")
    out.append(f"- Circuits with a literal `name :=` (graph nodes): "
               f"**{len(circuit_file)}**")
    out.append(f"- Compositional certificates (Lean registry): **{len(certs)}**")
    out.append(f"- Refinement atoms (Lean registry): **{len(refinements)}**")
    out.append(f"- Proof files: **{len(list(LEAN.rglob('*Proofs.lean')))}**")
    out.append("")
    out.append("Parameterised builders (`mkQueueNStructural`, `mkRegisterN`,")
    out.append("`mkMuxTree`, `mkDecoder`, ...) construct their circuit names by")
    out.append("interpolation, so those circuits cannot be recovered by scanning for a")
    out.append("literal; they are enumerated in `GenerateAll.lean` and are not graph")
    out.append("nodes here.  Everything below is derived from `lean/` alone, which is")
    out.append("what lets `lint` assert the map is current.")
    out.append("")

    out.append("## Subsystem composition")
    out.append("")
    out.append("Edges are circuit instantiations that cross a directory boundary; the")
    out.append("label is how many distinct instantiations cross it.")
    out.append("")
    out.append("```mermaid")
    out.append("graph TD")
    short = {s: s.replace("/", "_") for s in by_subsys}
    for s in sorted(by_subsys):
        out.append(f'  {short[s]}["{s}<br/>{len(by_subsys[s])} circuits"]')
    for (a, b), n in sorted(cross.items(), key=lambda kv: (-kv[1], kv[0])):
        out.append(f"  {short[a]} -->|{n}| {short[b]}")
    out.append("```")
    out.append("")

    out.append("## Coverage")
    out.append("")
    out.append("| Circuit | Subsystem | Inst. | Cert | Refines | Proofs | Doc |")
    out.append("| :--- | :--- | ---: | :---: | :---: | :---: | :---: |")
    for name in sorted(circuit_file):
        f = circuit_file[name]
        hdr = first_doc_header(file_text[f])
        out.append(
            "| `{n}` | {s} | {i} | {c} | {r} | {p} | {d} |".format(
                n=name,
                s=subsys_of[name],
                i=len(edges[name]),
                c="yes" if name in certs else "",
                r="yes" if name in refinements else "",
                p="yes" if has_proofs(name) else "",
                d="yes" if hdr else "",
            )
        )
    out.append("")

    out.append("## Mechanical gaps")
    out.append("")
    no_doc = [n for n in circuit_file if not first_doc_header(file_text[circuit_file[n]])]
    no_refine = [n for n in circuit_file if n not in refinements]
    no_proofs = [n for n in circuit_file if not has_proofs(n)]
    leaves = [n for n in circuit_file if not edges[n]]
    root_like = [n for n in circuit_file if not any(n in kids for kids in edges.values())]
    out.append(f"- **{len(no_doc)}** circuit files without a leading doc comment")
    out.append(f"- **{len(no_refine)}** circuits with no `Circuit satisfies Behavior` atom")
    out.append(f"- **{len(no_proofs)}** circuits with no `*Proofs.lean` mentioning them")
    out.append(f"- **{len(leaves)}** circuits that instantiate nothing (leaves)")
    out.append(f"- **{len(root_like)}** circuits nothing else instantiates (tops)")
    if no_doc:
        out.append("")
        out.append("<details><summary>files without a doc comment</summary>")
        out.append("")
        for n in sorted(no_doc):
            out.append(f"- `{circuit_file[n].relative_to(ROOT)}`")
        out.append("")
        out.append("</details>")
    out.append("")

    out.append("## Known gaps (hand-maintained)")
    out.append("")
    out.append("Not derivable from the tree; keep this list short and delete entries as")
    out.append("they land.")
    out.append("")
    for g in KNOWN_GAPS:
        out.append(f"- {g}")
    out.append("")

    dest = ROOT / args.out
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text("\n".join(out) + "\n")
    print(f"wrote {dest} ({len(out)} lines): {len(circuit_file)} circuits, "
          f"{len(certs)} certs, {len(no_doc)} undocumented, {len(no_proofs)} unproven")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
