#!/usr/bin/env python3
"""gen-bridges.py - Batch generate SMT2, Lean models, and proofs for leaf families."""

import subprocess
import re
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

REGISTERS = [1, 2, 3, 4, 6, 8, 12, 16, 20, 24, 32, 64, 96, 98, 130, 157, 158, 159, 160]
REGISTERS_EN = [1, 2, 4, 8, 16, 32, 64]
DECODERS = [2, 3, 4, 5, 6]
COMPARATORS = [4, 6, 32, 64]
SUBTRACTORS = [32, 64]

ADDER_TREES_32_64 = ["BrentKung", "CarrySelect", "HanCarlson", "KoggeStone", "RippleCarry", "Sklansky"]
ADDER_VARIANTS_32_64 = [
    ("", "Adder_spec.sv", True),
    ("NoCin", "AdderNoCin_spec.sv", False),
    ("WithCin1", "AdderWithCin1_spec.sv", False),
]
ADDER_TREES_106 = ["CarrySelect", "HanCarlson", "KoggeStone", "RippleCarry", "Sklansky"]
ADDER_VARIANTS_106 = [
    ("", "Adder_spec.sv", True),
    ("NoCin", "AdderNoCin_spec.sv", False),
]
EQUALITY_COMPARATORS = [6, 20, 32, 64]
MUX4 = [1, 32, 64]
MUX8 = [2, 32, 64]
MUX16 = [5, 6, 32]
MUX32 = [6]
MUX64 = [20, 32, 64]
LOGIC_UNITS = [4, 32, 64]
SHIFTERS = [(32, 5), (64, 6)]
PC_INCREMENTERS = [4, 8]

QUEUE1_FLOW = [39, 43, 44, 70, 71, 72, 75, 76, 103, 104]
QUEUE1_WIDTHS = [1, 8]
PRIORITY_ARBITERS = [2, 8, 64]
QUEUE_POINTERS = [3]
QUEUE_POINTERS_LOADABLE = [3]
QUEUE_COUNTERS_LOADABLE = [4]

# Purely combinational datapath units (no state): outputs compared directly.
# The IntegerExecUnits are compositional specs (two ALU32/ALU64 instances each);
# their spec-side dependencies are declared in SPEC_DEPS.
DATAPATH_UNITS = [
    "BranchExecUnit",
    "MemoryExecUnit",
    "MemoryExecUnitDecoupled",
    "CDBMux_FD_W2",
    "IntegerExecUnit_W2",
    "IntegerExecUnit_W2_64",
]

# Spec-side dependencies: specs that instantiate other specs need those
# sub-specs present when the spec is elaborated, otherwise Yosys leaves the
# submodule as a black box and the SMT2 model is self-referential.
SPEC_DEPS = {
    "IntegerExecUnit_W2": ["ALU32_spec.sv"],
    "IntegerExecUnit_W2_64": ["ALU64_spec.sv"],
}

# Queue16x32_DualPort: both designs hold the same 16 entries but flatten them
# into state fields in a different order.  The mapping below was derived by
# probing each state field through rd_data_0 (field -> entry index), so it is
# stable as long as both netlists are unchanged.
DUALPORT_IMPL_FIELDS = [
    "v_auto_ff_cc_337_slice_233", "v_auto_ff_cc_337_slice_245",
    "v_auto_ff_cc_337_slice_260", "v_auto_ff_cc_337_slice_257",
    "v_auto_ff_cc_337_slice_272", "v_auto_ff_cc_337_slice_251",
    "v_auto_ff_cc_337_slice_236", "v_auto_ff_cc_337_slice_230",
    "v_auto_ff_cc_337_slice_248", "v_auto_ff_cc_337_slice_239",
    "v_auto_ff_cc_337_slice_242", "v_auto_ff_cc_337_slice_275",
    "v_auto_ff_cc_337_slice_269", "v_auto_ff_cc_337_slice_254",
    "v_auto_ff_cc_337_slice_266", "v_auto_ff_cc_337_slice_263",
]
DUALPORT_SPEC_FIELDS = [
    "v_auto_ff_cc_337_slice_244", "v_auto_ff_cc_337_slice_246",
    "v_auto_ff_cc_337_slice_248", "v_auto_ff_cc_337_slice_250",
    "v_auto_ff_cc_337_slice_252", "v_auto_ff_cc_337_slice_254",
    "v_auto_ff_cc_337_slice_256", "v_auto_ff_cc_337_slice_241",
    "v_auto_ff_cc_337_slice_245", "v_auto_ff_cc_337_slice_249",
    "v_auto_ff_cc_337_slice_253", "v_auto_ff_cc_337_slice_240",
    "v_auto_ff_cc_337_slice_247", "v_auto_ff_cc_337_slice_255",
    "v_auto_ff_cc_337_slice_251", "v_auto_ff_cc_337_slice_243",
]
# spec entry j is held in impl field DUALPORT_IMPL_FIELDS[DUALPORT_ENTRY_TO_IMPL[j]]
DUALPORT_ENTRY_TO_IMPL = [0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 8, 9, 14, 10, 15]

def run(cmd):
    res = subprocess.run(cmd, shell=True, cwd=ROOT, capture_output=True, text=True)
    if res.returncode != 0:
        print(f"FAILED: {cmd}\n{res.stderr}")
        raise RuntimeError(res.stderr)

SV_DIR = Path(os.environ.get("SV_DIR", ROOT / "output" / "sv-from-lean"))


def sv_deps(mod):
    seen, stack = set(), [mod]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        f = SV_DIR / f"{m}.sv"
        if not f.exists():
            continue
        for inst in re.findall(r"^\s*([A-Za-z_]\w*)\s+[A-Za-z_]\w*\s*\(", f.read_text(), re.M):
            if (SV_DIR / f"{inst}.sv").exists() and inst not in seen:
                stack.append(inst)
    return " ".join(str(SV_DIR / f"{m}.sv") for m in sorted(seen))
TARGET_MODULES = set(sys.argv[1:]) if len(sys.argv) > 1 else None

SMT2LEAN_PATH = os.environ.get("SMT2LEAN")
if SMT2LEAN_PATH:
    SMT2LEAN_BIN = Path(SMT2LEAN_PATH).resolve()
    SMT2LEAN_CMD = str(SMT2LEAN_BIN)
else:
    SMT2LEAN_BIN = ROOT / "bazel-bin" / "smt2lean"
    if not SMT2LEAN_BIN.exists():
        subprocess.run(["bazel", "build", "//:smt2lean"], cwd=ROOT, check=True)
    SMT2LEAN_CMD = str(SMT2LEAN_BIN)

SVA2LEAN_PATH = os.environ.get("SVA2LEAN")
if SVA2LEAN_PATH:
    SVA2LEAN_BIN = Path(SVA2LEAN_PATH).resolve()
    SVA2LEAN_CMD = str(SVA2LEAN_BIN)
else:
    SVA2LEAN_BIN = ROOT / "bazel-bin" / "sva2lean"
    if not SVA2LEAN_BIN.exists():
        subprocess.run(["bazel", "build", "//:sva2lean"], cwd=ROOT, check=True)
    SVA2LEAN_CMD = str(SVA2LEAN_BIN) 
GEN_SCRIPT = Path(__file__).resolve()

def sv_dep_paths(mod):
    seen, stack = set(), [mod]
    paths = []
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        f = SV_DIR / f"{m}.sv"
        if not f.exists():
            continue
        paths.append(f)
        for inst in re.findall(r"^\s*([A-Za-z_]\w*)\s+[A-Za-z_]\w*\s*\(", f.read_text(), re.M):
            if (SV_DIR / f"{inst}.sv").exists() and inst not in seen:
                stack.append(inst)
    return paths

def is_up_to_date(targets, sources):
    for t in targets:
        if not t.exists():
            return False
    valid_sources = [s for s in sources if s.exists()]
    if not valid_sources:
        return True
    oldest_target = min(t.stat().st_mtime for t in targets)
    newest_source = max(s.stat().st_mtime for s in valid_sources)
    return oldest_target >= newest_source

SPEC_SVA_REPS = {}

def note_spec_rep(spec_file, mod, width):
    SPEC_SVA_REPS.setdefault((spec_file, width), mod)

def should_skip_bridge(mod, spec_file, note_w=None):
    if TARGET_MODULES and mod not in TARGET_MODULES:
        return True
    if note_w is not None and spec_file is not None:
        note_spec_rep(spec_file, mod, note_w)
    spec_sv = (ROOT / "verification" / "specs" / spec_file) if spec_file else None
    targets = [
        ROOT / f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean",
        ROOT / f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean",
        ROOT / f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean",
    ]
    sources = [SMT2LEAN_BIN, GEN_SCRIPT] + sv_dep_paths(mod)
    if spec_sv and spec_sv.exists():
        sources.append(spec_sv)
    return is_up_to_date(targets, sources)


def bridge_register(w, mod_name=None):
    mod = mod_name if mod_name is not None else f"Register{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Register_spec.sv", w):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Register_spec.sv; chparam -set WIDTH {w} Register_spec; hierarchy -top Register_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Register_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    spec_code = (ROOT / spec_lean).read_text()
    impl_code = (ROOT / impl_lean).read_text()

    s_field = re.search(r"structure State where\s*\n\s*(\w+)\s*:", spec_code).group(1)
    impl_state_block = re.search(r"structure State where(.*?)(?:deriving|def)", impl_code, re.DOTALL).group(1)
    i_fields = [m.group(1) for m in re.finditer(r"(\w+)\s*:\s*BitVec", impl_state_block)]
    concat_expr = " ++ ".join(f"s.{f}" for f in i_fields)
    st_pattern = ", ".join(f"s_{f}" for f in i_fields)

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  d := i.d
  clock := i.clock
  reset := i.reset
def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  {s_field} := {concat_expr}

/-- Equivalence: {mod} netlist refines parameterized Register_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.q = spc.1.q ∧
    absState imp.2 = spc.2 := by
  obtain ⟨d, clk, rst⟩ := i
  obtain ⟨{st_pattern}⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("Register_spec.sv", mod, w)

def bridge_register_en(w):
    mod = f"RegisterEn{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "RegisterEn_spec.sv", w):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/RegisterEn_spec.sv; chparam -set WIDTH {w} RegisterEn_spec; hierarchy -top RegisterEn_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} RegisterEn_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    spec_code = (ROOT / spec_lean).read_text()
    impl_code = (ROOT / impl_lean).read_text()

    s_field = re.search(r"structure State where\s*\n\s*(\w+)\s*:", spec_code).group(1)
    i_field = re.search(r"structure State where\s*\n\s*(\w+)\s*:", impl_code).group(1)

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  d := i.d
  en := i.en
  clock := i.clock
  reset := i.reset
def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  {s_field} := s.{i_field}

/-- Equivalence: {mod} netlist refines parameterized RegisterEn_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.q = spc.1.q ∧
    absState imp.2 = spc.2 := by
  obtain ⟨d, en, clk, rst⟩ := i
  obtain ⟨st⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("RegisterEn_spec.sv", mod, w)

def bridge_decoder(w):
    mod = f"Decoder{w}"
    out_w = 1 << w
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Decoder_spec.sv", w):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Decoder_spec.sv; chparam -set IN_WIDTH {w} -set OUT_WIDTH {out_w} Decoder_spec; hierarchy -top Decoder_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Decoder_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  «in» := i.«in»

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized Decoder_spec #({w}, {out_w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.out = spc.1.out := by
  obtain ⟨inp⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("Decoder_spec.sv", mod, w)

def bridge_comparator(w):
    mod = f"Comparator{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Comparator_spec.sv", w):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Comparator_spec.sv; chparam -set WIDTH {w} Comparator_spec; hierarchy -top Comparator_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    if w in (32, 64):
        run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_verilog /tmp/flat_{mod}.sv"')
        run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS /tmp/flat_{mod}.sv; hierarchy -top {mod}; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    else:
        run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Comparator_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  a := i.a
  b := i.b

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized Comparator_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.eq = spc.1.eq ∧
    imp.1.lt = spc.1.lt ∧
    imp.1.ltu = spc.1.ltu ∧
    imp.1.gt = spc.1.gt ∧
    imp.1.gtu = spc.1.gtu := by
  obtain ⟨a, b⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("Comparator_spec.sv", mod, w)
def bridge_subtractor(w):
    mod = f"Subtractor{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Subtractor_spec.sv", w):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Subtractor_spec.sv; chparam -set WIDTH {w} Subtractor_spec; hierarchy -top Subtractor_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Subtractor_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  a := i.a
  b := i.b

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines parameterized Subtractor_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.diff = spc.1.diff := by
  obtain ⟨a, b⟩ := i
  obtain ⟨⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("Subtractor_spec.sv", mod, w)

def bridge_adder(mod, spec_file, w, has_cin):
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, spec_file, w):
        return

    spec_name = spec_file.replace(".sv", "")
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/{spec_file}; chparam -set WIDTH {w} {spec_name}; hierarchy -top {spec_name}; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {spec_name} ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    impl_text = (ROOT / impl_lean).read_text()
    has_individual_sum = "sum_0 :" in impl_text

    cin_field = "\n  cin := i.cin" if has_cin else ""
    cin_pattern = "⟨a, b, cin⟩" if has_cin else "⟨a, b⟩"

    if has_individual_sum:
        sum_equality = " ∧\n".join([f"    imp.1.sum_{idx} = (BitVec.extractLsb' {idx} 1 spc.1.sum)" for idx in range(w)])
    else:
        sum_equality = "    imp.1.sum = spc.1.sum"

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  a := i.a
  b := i.b{cin_field}

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines parameterized {spec_name} #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
{sum_equality} := by
  obtain {cin_pattern} := i
  obtain ⟨⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep(spec_file, mod, w)
def bridge_full_adder():
    mod = "FullAdder"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "FullAdder_spec.sv", 1):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/FullAdder_spec.sv; hierarchy -top FullAdder_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} FullAdder_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  a := i.a
  b := i.b
  cin := i.cin

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines FullAdder_spec. -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.sum = spc.1.sum ∧
    imp.1.cout = spc.1.cout := by
  obtain ⟨a, b, cin⟩ := i
  obtain ⟨⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("FullAdder_spec.sv", mod, 1)

def bridge_ripple_carry_adder4():
    mod = "RippleCarryAdder4"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "RippleCarryAdder4_spec.sv", 4):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/RippleCarryAdder4_spec.sv; hierarchy -top RippleCarryAdder4_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} RippleCarryAdder4_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  a := i.a
  b := i.b
  cin := i.cin

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines RippleCarryAdder4_spec. -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.sum = spc.1.sum ∧
    imp.1.cout = spc.1.cout := by
  obtain ⟨a, b, cin⟩ := i
  obtain ⟨⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("RippleCarryAdder4_spec.sv", mod, 4)

def bridge_mul_final_adder64():
    mod = "MulFinalAdder64"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "MulFinalAdder64_spec.sv", 64):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/MulFinalAdder64_spec.sv; hierarchy -top MulFinalAdder64_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} MulFinalAdder64_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  a := i.a
  b := i.b

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines MulFinalAdder64_spec. -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.sum = spc.1.sum := by
  obtain ⟨a, b⟩ := i
  obtain ⟨⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("MulFinalAdder64_spec.sv", mod, 64)

def bridge_branch_target_adder32():
    mod = "BranchTargetAdder32"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "BranchTargetAdder32_spec.sv", 32):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/BranchTargetAdder32_spec.sv; hierarchy -top BranchTargetAdder32_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} BranchTargetAdder32_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  pc := i.pc
  instr := i.instr
  is_jal := i.is_jal

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines BranchTargetAdder32_spec. -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.target = spc.1.target := by
  obtain ⟨pc, instr, is_jal⟩ := i
  obtain ⟨⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("BranchTargetAdder32_spec.sv", mod, 32)
def bridge_csa_compressor(w):
    mod = f"CSACompressor{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "CSACompressor_spec.sv", w):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/CSACompressor_spec.sv; chparam -set WIDTH {w} CSACompressor_spec; hierarchy -top CSACompressor_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} CSACompressor_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  x := i.x
  y := i.y
  z := i.z

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines parameterized CSACompressor_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.sum = spc.1.sum ∧
    imp.1.carry = spc.1.carry := by
  obtain ⟨x, y, z⟩ := i
  obtain ⟨⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("CSACompressor_spec.sv", mod, w)

def bridge_alu(w):
    mod = f"ALU{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, f"{mod}_spec.sv", w):
        return

    spec_srcs = " ".join([f"verification/specs/{mod}_spec.sv"]
                          + [f"verification/specs/{d}" for d in SPEC_DEPS.get(mod, [])])
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {spec_srcs}; hierarchy -top {mod}_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {mod}_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  a := i.a
  b := i.b
  op := i.op

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines {mod}_spec. -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.result = spc.1.result := by
  obtain ⟨a, b, op⟩ := i
  obtain ⟨⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep(f"{mod}_spec.sv", mod, w)
def bridge_plru(ways):
    mod = f"PLRU{ways}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "PLRU_spec.sv", ways):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/PLRU_spec.sv; chparam -set WAYS {ways} PLRU_spec; hierarchy -top PLRU_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} PLRU_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    spec_code = (ROOT / spec_lean).read_text()
    impl_code = (ROOT / impl_lean).read_text()
    s_field = re.search(r"structure State where\s*\n\s*(\w+)\s*:", spec_code).group(1)
    i_field = re.search(r"structure State where\s*\n\s*(\w+)\s*:", impl_code).group(1)

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  clock := i.clock
  reset := i.reset
  upd_en := i.upd_en
  upd_way_oh := i.upd_way_oh

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  {s_field} := s.{i_field}

/-- Equivalence: {mod} netlist refines parameterized PLRU_spec #({ways}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.victim_oh = spc.1.victim_oh ∧
    absState imp.2 = spc.2 := by
  obtain ⟨clk, rst, upd_en, upd_way_oh⟩ := i
  obtain ⟨st⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("PLRU_spec.sv", mod, ways)

def bridge_rat(mod):
    spec = f"{mod}_spec"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, f"{spec}.sv", 32):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/{spec}.sv; hierarchy -top {spec}; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {spec} ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    for p in [ROOT / spec_lean, ROOT / impl_lean]:
        t = p.read_text()
        if "maxHeartbeats" not in t:
            t = t.replace("set_option maxRecDepth 262144\n", "set_option maxRecDepth 262144\nset_option maxHeartbeats 1000000\n")
            p.write_text(t)

    def get_entry_to_state_field(code):
        state_block = re.search(r'structure State where(.*?)(?:deriving|def)', code, re.DOTALL).group(1)
        state_fields = [m.group(1) for m in re.finditer(r'(\w+)\s*:\s*BitVec\s*6', state_block)]
        ret_match = re.search(r'\(\⟨.*?\⟩,\s*\⟨(.*?)⟩\)', code, re.DOTALL)
        next_syms = [x.strip() for x in ret_match.group(1).split(',')]
        sym_to_field = dict(zip(next_syms, state_fields))
        entry_to_field = {}
        for entry in range(32):
            bin_val = f"{entry:06b}"
            m = re.search(rf'let (\w+) := \(bif.*?0b{bin_val}#6.*?restore_data_{entry}', code)
            if not m:
                m = re.search(rf'let (\w+) := \(bif.*?restore_data_{entry}.*?0b{bin_val}#6', code)
            entry_to_field[entry] = sym_to_field[m.group(1)]
        return entry_to_field

    s_text = (ROOT / spec_lean).read_text()
    i_text = (ROOT / impl_lean).read_text()
    s_map = get_entry_to_state_field(s_text)
    i_map = get_entry_to_state_field(i_text)

    i_in_block = re.search(r'structure Inputs where(.*?)(?:deriving|structure)', i_text, re.DOTALL).group(1)
    in_fields = [m.group(1) for m in re.finditer(r'(\w+)\s*:\s*BitVec', i_in_block)]
    abs_inputs_body = "\n".join(f"  {f} := i.{f}" for f in in_fields)
    abs_state_body = "\n".join(f"  {s_map[e]} := s.{i_map[e]}" for e in range(32))

    i_state_block = re.search(r'structure State where(.*?)(?:deriving|def)', i_text, re.DOTALL).group(1)
    i_state_fields = [m.group(1) for m in re.finditer(r'(\w+)\s*:\s*BitVec', i_state_block)]
    st_pattern = ", ".join(f"s_{f}" for f in i_state_fields)
    in_pattern = ", ".join(f"i_{f}" for f in in_fields)

    out_block = re.search(r'structure Outputs where(.*?)(?:deriving|structure)', s_text, re.DOTALL).group(1)
    out_fields = [m.group(1) for m in re.finditer(r'(\w+)\s*:\s*BitVec', out_block)]
    out_conj = " ∧\n    ".join(f"imp.1.{f} = spc.1.{f}" for f in out_fields)

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 262144
set_option maxHeartbeats 2000000

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
{abs_inputs_body}

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
{abs_state_body}

theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    {out_conj} ∧
    absState imp.2 = spc.2 := by
  obtain ⟨{in_pattern}⟩ := i
  obtain ⟨{st_pattern}⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep(f"{spec}.sv", mod, 32)

def bridge_equality_comparator(w):
    mod = f"EqualityComparator{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "EqualityComparator_spec.sv", w):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/EqualityComparator_spec.sv; chparam -set WIDTH {w} EqualityComparator_spec; hierarchy -top EqualityComparator_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} EqualityComparator_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  a := i.a
  b := i.b

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized EqualityComparator_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.eq = spc.1.eq := by
  obtain ⟨a, b⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("EqualityComparator_spec.sv", mod, w)

def bridge_mux4(w):
    mod = f"Mux4x{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Mux4_spec.sv", w):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Mux4_spec.sv; chparam -set WIDTH {w} Mux4_spec; hierarchy -top Mux4_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Mux4_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  in0 := i.in0
  in1 := i.in1
  in2 := i.in2
  in3 := i.in3
  sel := i.sel

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized Mux4_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.out = spc.1.out := by
  obtain ⟨i0, i1, i2, i3, s_sel⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("Mux4_spec.sv", mod, w)

def bridge_mux8(w):
    mod = f"Mux8x{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Mux8_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Mux8_spec.sv; chparam -set WIDTH {w} Mux8_spec; hierarchy -top Mux8_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Mux8_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  in0 := i.in0
  in1 := i.in1
  in2 := i.in2
  in3 := i.in3
  in4 := i.in4
  in5 := i.in5
  in6 := i.in6
  in7 := i.in7
  sel := i.sel

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized Mux8_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.out = spc.1.out := by
  obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, s_sel⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_mux16(w):
    mod = f"Mux16x{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Mux16_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Mux16_spec.sv; chparam -set WIDTH {w} Mux16_spec; hierarchy -top Mux16_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Mux16_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    fields = "\n".join(f"  in{k} := i.in{k}" for k in range(16))
    bindings = ", ".join(f"i{k}" for k in range(16)) + ", s_sel"

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
{fields}
  sel := i.sel

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized Mux16_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.out = spc.1.out := by
  obtain ⟨{bindings}⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_mux32(w):
    mod = f"Mux32x{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Mux32_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Mux32_spec.sv; chparam -set WIDTH {w} Mux32_spec; hierarchy -top Mux32_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Mux32_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    fields = "\n".join(f"  in{k} := i.in{k}" for k in range(32))
    bindings = ", ".join(f"i{k}" for k in range(32)) + ", s_sel"

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
{fields}
  sel := i.sel

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized Mux32_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.out = spc.1.out := by
  obtain ⟨{bindings}⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_mux64(w):
    mod = f"Mux64x{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Mux64_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Mux64_spec.sv; chparam -set WIDTH {w} Mux64_spec; hierarchy -top Mux64_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Mux64_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    fields = "\n".join(f"  in{k} := i.in{k}" for k in range(64))
    bindings = ", ".join(f"i{k}" for k in range(64)) + ", s_sel"

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
{fields}
  sel := i.sel

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized Mux64_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.out = spc.1.out := by
  obtain ⟨{bindings}⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_logic_unit(w):
    mod = f"LogicUnit{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "LogicUnit_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/LogicUnit_spec.sv; chparam -set WIDTH {w} LogicUnit_spec; hierarchy -top LogicUnit_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} LogicUnit_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  a := i.a
  b := i.b
  op := i.op

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized LogicUnit_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.result = spc.1.result := by
  obtain ⟨a, b, op⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_shifter(w, shamt_w):
    mod = f"Shifter{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Shifter_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Shifter_spec.sv; chparam -set WIDTH {w} -set SHAMT_WIDTH {shamt_w} Shifter_spec; hierarchy -top Shifter_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Shifter_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  «in» := i.«in»
  shamt := i.shamt
  op := i.op

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized Shifter_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.result = spc.1.result := by
  obtain ⟨«in», shamt, op⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_pcincrementer(inc):
    mod = f"PCIncrementer{inc}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "PCIncrementer_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/PCIncrementer_spec.sv; chparam -set INC {inc} PCIncrementer_spec; hierarchy -top PCIncrementer_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} PCIncrementer_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  pc := i.pc

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State :=
  ⟨⟩

/-- Equivalence: {mod} netlist refines parameterized PCIncrementer_spec #({inc}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.pc_next = spc.1.pc_next := by
  obtain ⟨pc⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
# A spec's assertions are properties of the specification, so one instance per
# (spec, width) suffices: every circuit sharing an instantiation has an
# identical spec model.  Six adder topologies therefore produce one module, not
# six.  The first circuit seen at a given (spec, width) is the representative,
# and its model is the one the props module imports.
def emit_spec_sva():
    """Translate each spec's SVA assertions into Lean theorems over the Lean
    model of that same specification.  sva2lean exits non-zero rather than
    dropping an assertion."""
    count = 0
    for (spec_file, width), mod in sorted(SPEC_SVA_REPS.items()):
        spec_path = ROOT / "verification" / "specs" / spec_file
        if "assert" not in spec_path.read_text():
            continue
        model_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
        out_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}Props.lean"
        targets = [ROOT / out_lean]
        sources = [spec_path, ROOT / model_lean, SVA2LEAN_BIN, GEN_SCRIPT]
        if is_up_to_date(targets, sources):
            count += 1
            continue
        run(f'{SVA2LEAN_CMD} verification/specs/{spec_file} {model_lean} {out_lean}')
        print(f"Generated {mod}Props ({spec_file} at width {width})")
        count += 1
    print(f"Generated {count} spec assertion module(s)")

def bridge_queue1(w):
    mod = f"Queue1_{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Queue1_spec.sv", w):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Queue1_spec.sv; chparam -set WIDTH {w} Queue1_spec; hierarchy -top Queue1_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Queue1_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    spec_code = (ROOT / spec_lean).read_text()
    impl_code = (ROOT / impl_lean).read_text()

    spec_state_fields = re.findall(r"(\w+)\s*:\s*BitVec\s+(\d+)", spec_code[spec_code.find("structure State"):spec_code.find("def step")])
    impl_state_fields = re.findall(r"(\w+)\s*:\s*BitVec\s+(\d+)", impl_code[impl_code.find("structure State"):impl_code.find("def step")])

    s_map = {}
    for sf, sw in spec_state_fields:
        for imf, imw in impl_state_fields:
            if sw == imw and imf not in s_map.values():
                s_map[sf] = imf
                break

    abs_state_body = "\n".join(f"  {sf} := s.{imf}" for sf, imf in s_map.items())

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  enq_data := i.enq_data
  enq_valid := i.enq_valid
  deq_ready := i.deq_ready
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
{abs_state_body}

/-- Equivalence: {mod} netlist refines parameterized Queue1_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.enq_ready = spc.1.enq_ready ∧
    imp.1.valid = spc.1.valid ∧
    imp.1.data_reg = spc.1.data_reg ∧
    absState imp.2 = spc.2 := by
  obtain ⟨ed, ev, dr, clk, rst⟩ := i
  obtain ⟨d, v⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
    note_spec_rep("Queue1_spec.sv", mod, w)

def bridge_queue1_flow(w):
    mod = f"Queue1Flow_{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Queue1Flow_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Queue1Flow_spec.sv; chparam -set WIDTH {w} Queue1Flow_spec; hierarchy -top Queue1Flow_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Queue1Flow_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    spec_code = (ROOT / spec_lean).read_text()
    impl_code = (ROOT / impl_lean).read_text()

    spec_state_fields = re.findall(r"(\w+)\s*:\s*BitVec\s+(\d+)", spec_code[spec_code.find("structure State"):spec_code.find("def step")])
    impl_state_fields = re.findall(r"(\w+)\s*:\s*BitVec\s+(\d+)", impl_code[impl_code.find("structure State"):impl_code.find("def step")])

    s_map = {}
    for sf, sw in spec_state_fields:
        for imf, imw in impl_state_fields:
            if sw == imw and imf not in s_map.values():
                s_map[sf] = imf
                break

    abs_state_body = "\n".join(f"  {sf} := s.{imf}" for sf, imf in s_map.items())
    has_individual_deq = "deq_data_0 :" in impl_code
    if has_individual_deq:
        data_equality = " ∧\n".join([f"    imp.1.deq_data_{idx} = (BitVec.extractLsb' {idx} 1 spc.1.deq_data)" for idx in range(w)])
    else:
        data_equality = "    imp.1.deq_data = spc.1.deq_data"

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  enq_data := i.enq_data
  enq_valid := i.enq_valid
  deq_ready := i.deq_ready
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
{abs_state_body}

/-- Equivalence: {mod} netlist refines parameterized Queue1Flow_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.enq_ready = spc.1.enq_ready ∧
    imp.1.deq_valid = spc.1.deq_valid ∧
{data_equality} ∧
    absState imp.2 = spc.2 := by
  obtain ⟨ed, ev, dr, clk, rst⟩ := i
  obtain ⟨d, v⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_priority_arbiter(w):
    mod = f"PriorityArbiter{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "PriorityArbiter_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/PriorityArbiter_spec.sv; chparam -set WIDTH {w} PriorityArbiter_spec; hierarchy -top PriorityArbiter_spec; flatten; proc; opt; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} PriorityArbiter_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  request := i.request

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines parameterized PriorityArbiter_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.grant = spc.1.grant ∧
    imp.1.valid = spc.1.valid := by
  obtain ⟨req⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_one_hot_encoder():
    mod = "OneHotEncoder64"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "OneHotEncoder_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/OneHotEncoder_spec.sv; hierarchy -top OneHotEncoder_spec; flatten; proc; opt; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} OneHotEncoder_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  «in» := i.«in»

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines OneHotEncoder_spec #(64). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.out = spc.1.out := by
  obtain ⟨«in»⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_popcount():
    mod = "Popcount8"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Popcount_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Popcount_spec.sv; hierarchy -top Popcount_spec; flatten; proc; opt; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} Popcount_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  «in» := i.«in»

def absState (_ : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where

/-- Equivalence: {mod} netlist refines Popcount_spec #(8). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.count = spc.1.count := by
  obtain ⟨«in»⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_queue_pointer(w):
    mod = f"QueuePointer_{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "QueuePointer_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/QueuePointer_spec.sv; chparam -set WIDTH {w} QueuePointer_spec; hierarchy -top QueuePointer_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} QueuePointer_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    spec_code = (ROOT / spec_lean).read_text()
    impl_code = (ROOT / impl_lean).read_text()

    spec_sf = re.search(r"structure State where\s*\n\s*(\w+)\s*:", spec_code).group(1)
    impl_sf = re.search(r"structure State where\s*\n\s*(\w+)\s*:", impl_code).group(1)

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  en := i.en
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  {spec_sf} := s.{impl_sf}

/-- Equivalence: {mod} netlist refines parameterized QueuePointer_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.count = spc.1.count ∧
    absState imp.2 = spc.2 := by
  obtain ⟨en, clk, rst⟩ := i
  obtain ⟨cnt⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_queue_pointer_loadable(w):
    mod = f"QueuePointerLoadable_{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "QueuePointerLoadable_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/QueuePointerLoadable_spec.sv; chparam -set WIDTH {w} QueuePointerLoadable_spec; hierarchy -top QueuePointerLoadable_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} QueuePointerLoadable_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    spec_code = (ROOT / spec_lean).read_text()
    impl_code = (ROOT / impl_lean).read_text()

    spec_sf = re.search(r"structure State where\s*\n\s*(\w+)\s*:", spec_code).group(1)
    impl_sf = re.search(r"structure State where\s*\n\s*(\w+)\s*:", impl_code).group(1)

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  en := i.en
  load_en := i.load_en
  load_value := i.load_value
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  {spec_sf} := s.{impl_sf}

/-- Equivalence: {mod} netlist refines parameterized QueuePointerLoadable_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.count = spc.1.count ∧
    absState imp.2 = spc.2 := by
  obtain ⟨en, len, lval, clk, rst⟩ := i
  obtain ⟨cnt⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_queue_counter_loadable(w):
    mod = f"QueueCounterLoadable_{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "QueueCounterLoadable_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/QueueCounterLoadable_spec.sv; chparam -set WIDTH {w} QueueCounterLoadable_spec; hierarchy -top QueueCounterLoadable_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} QueueCounterLoadable_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    spec_code = (ROOT / spec_lean).read_text()
    impl_code = (ROOT / impl_lean).read_text()

    spec_sf = re.search(r"structure State where\s*\n\s*(\w+)\s*:", spec_code).group(1)
    impl_sf = re.search(r"structure State where\s*\n\s*(\w+)\s*:", impl_code).group(1)

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  inc := i.inc
  dec := i.dec
  load_en := i.load_en
  load_value := i.load_value
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  {spec_sf} := s.{impl_sf}

/-- Equivalence: {mod} netlist refines parameterized QueueCounterLoadable_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.count = spc.1.count ∧
    absState imp.2 = spc.2 := by
  obtain ⟨inc, dec, len, lval, clk, rst⟩ := i
  obtain ⟨cnt⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_dual_port_queue():
    mod = "Queue16x32_DualPort"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, "Queue16x32_DualPort_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/{mod}_spec.sv; hierarchy -top {mod}_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {mod}_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    spec_state_body = "\n".join(
        f"  {DUALPORT_SPEC_FIELDS[j]} := s.{DUALPORT_IMPL_FIELDS[DUALPORT_ENTRY_TO_IMPL[j]]}"
        for j in range(16))

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  wr_en := i.wr_en
  wr_idx_0 := i.wr_idx_0
  wr_data_0 := i.wr_data_0
  wr_idx_1 := i.wr_idx_1
  wr_data_1 := i.wr_data_1
  rd_idx_0 := i.rd_idx_0
  rd_idx_1 := i.rd_idx_1
  clock := i.clock
  reset := i.reset

/-- State abstraction: both sides hold the same 16 entries, but the flattened
    state field order differs.  Map entry j to the impl field that holds it. -/
def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
{spec_state_body}

/-- Equivalence: {mod} netlist refines the 16x32 dual-port register-file spec. -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.rd_data_0 = spc.1.rd_data_0 ∧
    imp.1.rd_data_1 = spc.1.rd_data_1 ∧
    absState imp.2 = spc.2 := by
  obtain ⟨we, wi0, wd0, wi1, wd1, ri0, ri1, clk, rst⟩ := i
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")
def bridge_resetsync():
    mod = "ResetSync"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, f"{mod}_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/{mod}_spec.sv; hierarchy -top {mod}_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {mod}_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  v_procdff_5 := s.v_procdff_5
  v_procdff_8 := s.v_procdff_8

theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.sync_reset = spc.1.sync_reset ∧
    absState imp.2 = spc.2 := by
  obtain ⟨clk, rst⟩ := i
  obtain ⟨s0, s1⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    note_spec_rep(f"{mod}_spec.sv", mod, None)
    print(f"Generated {mod}")


def bridge_bootrom():
    mod = "BootROM"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, f"{mod}_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/{mod}_spec.sv; hierarchy -top {mod}_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {mod}_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  bootrom_a_valid := i.bootrom_a_valid
  bootrom_a_opcode := i.bootrom_a_opcode
  bootrom_a_param := i.bootrom_a_param
  bootrom_a_size := i.bootrom_a_size
  bootrom_a_source := i.bootrom_a_source
  bootrom_a_address := i.bootrom_a_address
  bootrom_a_mask := i.bootrom_a_mask
  bootrom_a_data := i.bootrom_a_data
  bootrom_d_ready := i.bootrom_d_ready
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  v_procdff_6 := s.v_procdff_6

theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.bootrom_a_ready = spc.1.bootrom_a_ready ∧
    imp.1.bootrom_d_valid = spc.1.bootrom_d_valid ∧
    imp.1.bootrom_d_opcode = spc.1.bootrom_d_opcode ∧
    imp.1.bootrom_d_param = spc.1.bootrom_d_param ∧
    imp.1.bootrom_d_size = spc.1.bootrom_d_size ∧
    imp.1.bootrom_d_source = spc.1.bootrom_d_source ∧
    imp.1.bootrom_d_sink = spc.1.bootrom_d_sink ∧
    imp.1.bootrom_d_data = spc.1.bootrom_d_data ∧
    imp.1.bootrom_d_denied = spc.1.bootrom_d_denied ∧
    absState imp.2 = spc.2 := by
  obtain ⟨bav, bao, bap, bas, basrc, baa, bam, bad, bdr, clk, rst⟩ := i
  obtain ⟨s0⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    note_spec_rep(f"{mod}_spec.sv", mod, None)
    print(f"Generated {mod}")


def bridge_gpio():
    mod = "GPIO"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, f"{mod}_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/{mod}_spec.sv; hierarchy -top {mod}_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {mod}_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  gpio_a_valid := i.gpio_a_valid
  gpio_a_opcode := i.gpio_a_opcode
  gpio_a_param := i.gpio_a_param
  gpio_a_size := i.gpio_a_size
  gpio_a_source := i.gpio_a_source
  gpio_a_address := i.gpio_a_address
  gpio_a_mask := i.gpio_a_mask
  gpio_a_data := i.gpio_a_data
  gpio_d_ready := i.gpio_d_ready
  gpio_i := i.gpio_i
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  v_auto_ff_cc_337_slice_55 := s.v_auto_ff_cc_337_slice_53
  v_procdff_53 := s.v_procdff_52
  v_auto_ff_cc_337_slice_54 := s.v_auto_ff_cc_337_slice_56
  v_auto_ff_cc_337_slice_56 := s.v_auto_ff_cc_337_slice_59

theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.gpio_a_ready = spc.1.gpio_a_ready ∧
    imp.1.gpio_d_valid = spc.1.gpio_d_valid ∧
    imp.1.gpio_d_opcode = spc.1.gpio_d_opcode ∧
    imp.1.gpio_d_param = spc.1.gpio_d_param ∧
    imp.1.gpio_d_size = spc.1.gpio_d_size ∧
    imp.1.gpio_d_source = spc.1.gpio_d_source ∧
    imp.1.gpio_d_sink = spc.1.gpio_d_sink ∧
    imp.1.gpio_d_data = spc.1.gpio_d_data ∧
    imp.1.gpio_d_denied = spc.1.gpio_d_denied ∧
    imp.1.gpio_irq = spc.1.gpio_irq ∧
    imp.1.gpio_o = spc.1.gpio_o ∧
    imp.1.gpio_oen = spc.1.gpio_oen ∧
    absState imp.2 = spc.2 := by
  obtain ⟨gav, gao, gap, gas, gasrc, gaa, gam, gad, gdr, gi, clk, rst⟩ := i
  obtain ⟨s0, s1, s2, s3⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    note_spec_rep(f"{mod}_spec.sv", mod, None)
    print(f"Generated {mod}")


def bridge_uart():
    mod = "UART"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, f"{mod}_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/{mod}_spec.sv; hierarchy -top {mod}_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {mod}_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  uart_a_valid := i.uart_a_valid
  uart_a_opcode := i.uart_a_opcode
  uart_a_param := i.uart_a_param
  uart_a_size := i.uart_a_size
  uart_a_source := i.uart_a_source
  uart_a_address := i.uart_a_address
  uart_a_mask := i.uart_a_mask
  uart_a_data := i.uart_a_data
  uart_d_ready := i.uart_d_ready
  uart_rx := i.uart_rx
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  v_auto_ff_cc_337_slice_55 := s.v_auto_ff_cc_337_slice_76
  v_auto_ff_cc_337_slice_54 := s.v_auto_ff_cc_337_slice_70
  v_procdff_37 := s.v_auto_ff_cc_337_slice_69
  v_procdff_43 := s.v_procdff_50
  v_auto_ff_cc_337_slice_53 := s.v_auto_ff_cc_337_slice_73
  v_auto_ff_cc_337_slice_56 := s.v_auto_ff_cc_337_slice_60
  v_procdff_52 := s.v_procdff_59

theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.uart_a_ready = spc.1.uart_a_ready ∧
    imp.1.uart_d_valid = spc.1.uart_d_valid ∧
    imp.1.uart_d_opcode = spc.1.uart_d_opcode ∧
    imp.1.uart_d_param = spc.1.uart_d_param ∧
    imp.1.uart_d_size = spc.1.uart_d_size ∧
    imp.1.uart_d_source = spc.1.uart_d_source ∧
    imp.1.uart_d_sink = spc.1.uart_d_sink ∧
    imp.1.uart_d_data = spc.1.uart_d_data ∧
    imp.1.uart_d_denied = spc.1.uart_d_denied ∧
    imp.1.uart_tx = spc.1.uart_tx ∧
    imp.1.uart_irq = spc.1.uart_irq ∧
    absState imp.2 = spc.2 := by
  obtain ⟨uav, uao, uap, uas, uasrc, uaa, uam, uad, udr, urx, clk, rst⟩ := i
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    note_spec_rep(f"{mod}_spec.sv", mod, None)
    print(f"Generated {mod}")


def bridge_aclint():
    mod = "ACLINT"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, f"{mod}_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/{mod}_spec.sv; hierarchy -top {mod}_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {mod}_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  aclint_a_valid := i.aclint_a_valid
  aclint_a_opcode := i.aclint_a_opcode
  aclint_a_param := i.aclint_a_param
  aclint_a_size := i.aclint_a_size
  aclint_a_source := i.aclint_a_source
  aclint_a_address := i.aclint_a_address
  aclint_a_mask := i.aclint_a_mask
  aclint_a_data := i.aclint_a_data
  aclint_d_ready := i.aclint_d_ready
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  v_procdff_30 := s.v_procdff_172 ++ s.v_procdff_175
  v_auto_ff_cc_337_slice_44 := s.v_auto_ff_cc_337_slice_188 ++ s.v_auto_ff_cc_337_slice_179
  v_auto_ff_cc_337_slice_43 := s.v_auto_ff_cc_337_slice_185
  v_auto_ff_cc_337_slice_45 := s.v_auto_ff_cc_337_slice_182
  v_procdff_42 := s.v_procdff_178

theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.aclint_a_ready = spc.1.aclint_a_ready ∧
    imp.1.aclint_d_valid = spc.1.aclint_d_valid ∧
    imp.1.aclint_d_opcode = spc.1.aclint_d_opcode ∧
    imp.1.aclint_d_param = spc.1.aclint_d_param ∧
    imp.1.aclint_d_size = spc.1.aclint_d_size ∧
    imp.1.aclint_d_source = spc.1.aclint_d_source ∧
    imp.1.aclint_d_sink = spc.1.aclint_d_sink ∧
    imp.1.aclint_d_data = spc.1.aclint_d_data ∧
    imp.1.aclint_d_denied = spc.1.aclint_d_denied ∧
    imp.1.mtip_out = spc.1.mtip_out ∧
    imp.1.msip_out = spc.1.msip_out ∧
    imp.1.ssip_out = spc.1.ssip_out ∧
    absState imp.2 = spc.2 := by
  obtain ⟨aav, aao, aap, aas, aasrc, aaa, aam, aad, adr, clk, rst⟩ := i
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    note_spec_rep(f"{mod}_spec.sv", mod, None)
    print(f"Generated {mod}")


def bridge_aplic():
    mod = "APLIC"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, f"{mod}_spec.sv", None):
        return

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/{mod}_spec.sv; hierarchy -top {mod}_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {mod}_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
  aplic_a_valid := i.aplic_a_valid
  aplic_a_opcode := i.aplic_a_opcode
  aplic_a_param := i.aplic_a_param
  aplic_a_size := i.aplic_a_size
  aplic_a_source := i.aplic_a_source
  aplic_a_address := i.aplic_a_address
  aplic_a_mask := i.aplic_a_mask
  aplic_a_data := i.aplic_a_data
  aplic_d_ready := i.aplic_d_ready
  irq_src := i.irq_src
  clock := i.clock
  reset := i.reset

def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  v_auto_ff_cc_337_slice_40 := s.v_auto_ff_cc_337_slice_60
  v_auto_ff_cc_337_slice_36 := s.v_auto_ff_cc_337_slice_51
  v_auto_ff_cc_337_slice_35 := s.v_auto_ff_cc_337_slice_54
  v_procdff_34 := s.v_procdff_50

theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.aplic_a_ready = spc.1.aplic_a_ready ∧
    imp.1.aplic_d_valid = spc.1.aplic_d_valid ∧
    imp.1.aplic_d_opcode = spc.1.aplic_d_opcode ∧
    imp.1.aplic_d_param = spc.1.aplic_d_param ∧
    imp.1.aplic_d_size = spc.1.aplic_d_size ∧
    imp.1.aplic_d_source = spc.1.aplic_d_source ∧
    imp.1.aplic_d_sink = spc.1.aplic_d_sink ∧
    imp.1.aplic_d_data = spc.1.aplic_d_data ∧
    imp.1.aplic_d_denied = spc.1.aplic_d_denied ∧
    imp.1.meip_out = spc.1.meip_out ∧
    imp.1.seip_out = spc.1.seip_out ∧
    absState imp.2 = spc.2 := by
  obtain ⟨aav, aao, aap, aas, aasrc, aaa, aam, aad, adr, isrc, clk, rst⟩ := i
  obtain ⟨s0, s1, s2, s3⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState,
             ShoumeiSec.Bridge.{mod}Spec.State.mk.injEq]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    note_spec_rep(f"{mod}_spec.sv", mod, None)
    print(f"Generated {mod}")


def bridge_datapath(mod):
    """Stateless (purely combinational) datapath unit: no state, outputs only.

    Both models are single-cycle functions, so the proof compares every output
    for an arbitrary input vector (no state abstraction needed)."""
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"
    if should_skip_bridge(mod, f"{mod}_spec.sv", None):
        return

    spec_srcs = " ".join([f"verification/specs/{mod}_spec.sv"]
                          + [f"verification/specs/{d}" for d in SPEC_DEPS.get(mod, [])])
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {spec_srcs}; hierarchy -top {mod}_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'{SMT2LEAN_CMD} {spec_smt} {mod}_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'{SMT2LEAN_CMD} {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

    # Composed models (e.g. an exec unit flattening two ALUs) need a deeper
    # definitional-equality budget than the smt2lean default.
    for gen_lean in (spec_lean, impl_lean):
        gp = ROOT / gen_lean
        gt = gp.read_text()
        if "maxHeartbeats" not in gt:
            gp.write_text(gt.replace("set_option maxRecDepth 262144",
                                     "set_option maxRecDepth 262144\nset_option maxHeartbeats 4000000", 1))

    s_text = (ROOT / spec_lean).read_text()
    i_text = (ROOT / impl_lean).read_text()
    in_block = re.search(r"structure Inputs where(.*?)(?:deriving|structure)", s_text, re.DOTALL).group(1)
    in_fields = [m.group(1) for m in re.finditer(r"(\w+)\s*:\s*BitVec", in_block)]
    out_block = re.search(r"structure Outputs where(.*?)(?:deriving|structure)", s_text, re.DOTALL).group(1)
    out_fields = [m.group(1) for m in re.finditer(r"(\w+)\s*:\s*BitVec", out_block)]
    out_conj = " ∧\n    ".join(f"imp.1.{f} = spc.1.{f}" for f in out_fields)
    in_pattern = ", ".join(f"i_{f}" for f in in_fields)

    proof_content = f"""import ShoumeiSec.Bridge.{mod}Spec
import ShoumeiSec.Bridge.{mod}Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.Bridge{mod}

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 262144

def absInputs (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    ShoumeiSec.Bridge.{mod}Spec.Inputs where
{chr(10).join(f"  {f} := i.{f}" for f in in_fields)}

/-- Equivalence: {mod} is purely combinational, so every output must agree on
    every input vector (no state to abstract). -/
theorem {mod.lower()}_sec (i : ShoumeiSec.Bridge.{mod}Impl.Inputs) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i default
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) default
    {out_conj} := by
  obtain ⟨{in_pattern}⟩ := i
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    note_spec_rep(f"{mod}_spec.sv", mod, None)
    print(f"Generated {mod}")


def main():
    (ROOT / "verification" / "bridge").mkdir(parents=True, exist_ok=True)
    (ROOT / "output" / "sec-bridge" / "ShoumeiSec" / "Bridge").mkdir(parents=True, exist_ok=True)
    print("Generating Register bridges...")
    for w in REGISTERS:
        bridge_register(w)
    bridge_register(1, mod_name="DFlipFlop")
    bridge_register(160, mod_name="Register160Flat")
    print("Generating RegisterEn bridges...")
    for w in REGISTERS_EN:
        bridge_register_en(w)
    print("Generating Decoder bridges...")
    for w in DECODERS:
        bridge_decoder(w)
    print("Generating Comparator bridges...")
    for w in COMPARATORS:
        bridge_comparator(w)
    print("Generating Subtractor bridges...")
    for w in SUBTRACTORS:
        bridge_subtractor(w)
    print("Generating Adder bridges...")
    for w in [32, 64]:
        for t in ADDER_TREES_32_64:
            for v, spec_file, has_cin in ADDER_VARIANTS_32_64:
                bridge_adder(f"{t}Adder{w}{v}", spec_file, w, has_cin)
    for t in ADDER_TREES_106:
        for v, spec_file, has_cin in ADDER_VARIANTS_106:
            bridge_adder(f"{t}Adder106{v}", spec_file, 106, has_cin)
    print("Generating Small Adder bridges...")
    bridge_full_adder()
    bridge_ripple_carry_adder4()
    bridge_mul_final_adder64()
    bridge_branch_target_adder32()
    print("Generating CSACompressor bridges...")
    for w in [48, 64, 106]:
        bridge_csa_compressor(w)
    print("Generating ALU bridges...")
    bridge_alu(32)
    bridge_alu(64)
    print("Generating PLRU bridges...")
    for w in [2, 4, 8]:
        bridge_plru(w)
    print("Generating RAT bridges...")
    for mod in ["CRAT_32x6", "IntRAT_32x6", "RAT_32x6"]:
        bridge_rat(mod)
    print("Generating EqualityComparator bridges...")
    for w in EQUALITY_COMPARATORS:
        bridge_equality_comparator(w)
    print("Generating Mux4 bridges...")
    for w in MUX4:
        bridge_mux4(w)
    print("Generating Mux8 bridges...")
    for w in MUX8:
        bridge_mux8(w)
    print("Generating Mux16 bridges...")
    for w in MUX16:
        bridge_mux16(w)
    print("Generating Mux32 bridges...")
    for w in MUX32:
        bridge_mux32(w)
    print("Generating Mux64 bridges...")
    for w in MUX64:
        bridge_mux64(w)
    print("Generating LogicUnit bridges...")
    for w in LOGIC_UNITS:
        bridge_logic_unit(w)
    print("Generating Shifter bridges...")
    for w, shamt_w in SHIFTERS:
        bridge_shifter(w, shamt_w)
    print("Generating PCIncrementer bridges...")
    for inc in PC_INCREMENTERS:
        bridge_pcincrementer(inc)
    print("Generating Queue1 bridges...")
    for w in QUEUE1_WIDTHS:
        bridge_queue1(w)
    print("Generating Queue1Flow bridges...")
    for w in QUEUE1_FLOW:
        bridge_queue1_flow(w)
    print("Generating PriorityArbiter bridges...")
    for w in PRIORITY_ARBITERS:
        bridge_priority_arbiter(w)
    print("Generating OneHotEncoder bridges...")
    bridge_one_hot_encoder()
    print("Generating Popcount bridges...")
    bridge_popcount()
    print("Generating QueuePointer bridges...")
    for w in QUEUE_POINTERS:
        bridge_queue_pointer(w)
    print("Generating QueuePointerLoadable bridges...")
    for w in QUEUE_POINTERS_LOADABLE:
        bridge_queue_pointer_loadable(w)
    print("Generating QueueCounterLoadable bridges...")
    for w in QUEUE_COUNTERS_LOADABLE:
        bridge_queue_counter_loadable(w)
    print("Generating Queue16x32_DualPort bridges...")
    bridge_dual_port_queue()
    print("Generating Peripheral bridges...")
    bridge_resetsync()
    bridge_bootrom()
    bridge_gpio()
    bridge_uart()
    bridge_aclint()
    bridge_aplic()
    print("Generating Datapath bridges...")
    for mod in DATAPATH_UNITS:
        bridge_datapath(mod)
    emit_spec_sva()
    proof_files = sorted((ROOT / "output" / "sec-bridge" / "ShoumeiSec").glob("Bridge*.lean"))
    lines = ["-- Generated root for ShoumeiSec bridge library", ""]
    for pf in proof_files:
        lines.append(f"import ShoumeiSec.{pf.stem}")
    (ROOT / "output" / "sec-bridge" / "ShoumeiSec.lean").write_text("\n".join(lines) + "\n")
    print(f"Generated ShoumeiSec.lean with {len(proof_files)} proofs")

if __name__ == "__main__":
    main()
