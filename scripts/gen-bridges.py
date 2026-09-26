#!/usr/bin/env python3
"""gen-bridges.py - Batch generate SMT2, Lean models, and proofs for leaf families."""

import subprocess
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

REGISTERS = [1, 2, 3, 4, 6, 8, 12, 16, 20, 24, 32, 64]
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

def run(cmd):
    res = subprocess.run(cmd, shell=True, cwd=ROOT, capture_output=True, text=True)
    if res.returncode != 0:
        print(f"FAILED: {cmd}\n{res.stderr}")
        raise RuntimeError(res.stderr)

SV_DIR = ROOT / "output" / "sv-from-lean"
(ROOT / "verification" / "bridge").mkdir(parents=True, exist_ok=True)
(ROOT / "output" / "sec-bridge" / "ShoumeiSec" / "Bridge").mkdir(parents=True, exist_ok=True)


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

def bridge_register(w):
    mod = f"Register{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Register_spec.sv; chparam -set WIDTH {w} Register_spec; hierarchy -top Register_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} Register_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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
  clock := i.clock
  reset := i.reset
def absState (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    ShoumeiSec.Bridge.{mod}Spec.State where
  {s_field} := s.{i_field}

/-- Equivalence: {mod} netlist refines parameterized Register_spec #({w}). -/
theorem {mod.lower()}_sec
    (i : ShoumeiSec.Bridge.{mod}Impl.Inputs)
    (s : ShoumeiSec.Bridge.{mod}Impl.State) :
    let imp := ShoumeiSec.Bridge.{mod}Impl.step i s
    let spc := ShoumeiSec.Bridge.{mod}Spec.step (absInputs i) (absState s)
    imp.1.q = spc.1.q ∧
    absState imp.2 = spc.2 := by
  obtain ⟨d, clk, rst⟩ := i
  obtain ⟨st⟩ := s
  simp only [ShoumeiSec.Bridge.{mod}Impl.step,
             ShoumeiSec.Bridge.{mod}Spec.step,
             absInputs, absState]
  bv_decide

end ShoumeiSec.Bridge{mod}
"""
    (ROOT / proof_lean).write_text(proof_content)
    print(f"Generated {mod}")

def bridge_register_en(w):
    mod = f"RegisterEn{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/RegisterEn_spec.sv; chparam -set WIDTH {w} RegisterEn_spec; hierarchy -top RegisterEn_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} RegisterEn_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

def bridge_decoder(w):
    mod = f"Decoder{w}"
    out_w = 1 << w
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Decoder_spec.sv; chparam -set IN_WIDTH {w} -set OUT_WIDTH {out_w} Decoder_spec; hierarchy -top Decoder_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} Decoder_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

def bridge_comparator(w):
    mod = f"Comparator{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Comparator_spec.sv; chparam -set WIDTH {w} Comparator_spec; hierarchy -top Comparator_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    if w in (32, 64):
        run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_verilog /tmp/flat_{mod}.sv"')
        run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS /tmp/flat_{mod}.sv; hierarchy -top {mod}; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    else:
        run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} Comparator_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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
def bridge_subtractor(w):
    mod = f"Subtractor{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Subtractor_spec.sv; chparam -set WIDTH {w} Subtractor_spec; hierarchy -top Subtractor_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} Subtractor_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

def bridge_adder(mod, spec_file, w, has_cin):
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"

    spec_name = spec_file.replace(".sv", "")
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/{spec_file}; chparam -set WIDTH {w} {spec_name}; hierarchy -top {spec_name}; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} {spec_name} ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

def bridge_equality_comparator(w):
    mod = f"EqualityComparator{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/EqualityComparator_spec.sv; chparam -set WIDTH {w} EqualityComparator_spec; hierarchy -top EqualityComparator_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} EqualityComparator_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

def bridge_mux4(w):
    mod = f"Mux4x{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Mux4_spec.sv; chparam -set WIDTH {w} Mux4_spec; hierarchy -top Mux4_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} Mux4_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

def bridge_mux8(w):
    mod = f"Mux8x{w}"
    spec_smt = f"verification/bridge/{mod}_spec.smt2"
    impl_smt = f"verification/bridge/{mod}_impl.smt2"
    spec_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Spec.lean"
    impl_lean = f"output/sec-bridge/ShoumeiSec/Bridge/{mod}Impl.lean"
    proof_lean = f"output/sec-bridge/ShoumeiSec/Bridge{mod}.lean"

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Mux8_spec.sv; chparam -set WIDTH {w} Mux8_spec; hierarchy -top Mux8_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} Mux8_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Mux16_spec.sv; chparam -set WIDTH {w} Mux16_spec; hierarchy -top Mux16_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} Mux16_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Mux32_spec.sv; chparam -set WIDTH {w} Mux32_spec; hierarchy -top Mux32_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} Mux32_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Mux64_spec.sv; chparam -set WIDTH {w} Mux64_spec; hierarchy -top Mux64_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} Mux64_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/LogicUnit_spec.sv; chparam -set WIDTH {w} LogicUnit_spec; hierarchy -top LogicUnit_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} LogicUnit_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/Shifter_spec.sv; chparam -set WIDTH {w} -set SHAMT_WIDTH {shamt_w} Shifter_spec; hierarchy -top Shifter_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} Shifter_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS verification/specs/PCIncrementer_spec.sv; chparam -set INC {inc} PCIncrementer_spec; hierarchy -top PCIncrementer_spec; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {spec_smt}"')
    run(f'yosys -q -p "read_verilog -sv -D SYNTHESIS {sv_deps(mod)}; hierarchy -top {mod}; setattr -mod -unset keep_hierarchy; flatten; proc; opt; async2sync; dffunmap; formalff -clk2ff; opt_clean; write_functional_smt2 {impl_smt}"')
    run(f'lake exe smt2lean {spec_smt} PCIncrementer_spec ShoumeiSec.Bridge.{mod}Spec {spec_lean}')
    run(f'lake exe smt2lean {impl_smt} {mod} ShoumeiSec.Bridge.{mod}Impl {impl_lean}')

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

def main():
    print("Generating Register bridges...")
    for w in REGISTERS:
        bridge_register(w)
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

    proof_files = sorted((ROOT / "output" / "sec-bridge" / "ShoumeiSec").glob("Bridge*.lean"))
    lines = ["-- Generated root for ShoumeiSec bridge library", ""]
    for pf in proof_files:
        lines.append(f"import ShoumeiSec.{pf.stem}")
    (ROOT / "output" / "sec-bridge" / "ShoumeiSec.lean").write_text("\n".join(lines) + "\n")
    print(f"Generated ShoumeiSec.lean with {len(proof_files)} proofs")

if __name__ == "__main__":
    main()
