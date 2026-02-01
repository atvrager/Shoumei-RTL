# SystemC Backend Implementation Plan

## Overview

Add a SystemC code generation backend to Shoumei RTL, enabling **triple equivalence checking**:
- LEAN SV ≡ Chisel SV (structural LEC via Yosys)
- SystemC ≡ LEAN SV (behavioral equivalence via VCD comparison)

**Scope**: All 23 existing modules (combinational + sequential)
**Signal Types**: `sc_signal<bool>` only (single-bit, consistent with current DSL)
**Verification**: VCD-based behavioral equivalence with test vectors extracted from LEAN proofs
**Timeline**: 5 phases (can be adjusted based on complexity)

---

## Architecture Decisions

### 1. Code Generation Pattern
Follow existing SystemVerilog/Chisel generator structure:
- **Input**: Circuit DSL (Wire, Gate, Circuit)
- **Output**: SystemC `.h` (header) + `.cpp` (implementation) files
- **Reuse**: Common utilities (`indent`, `joinLines`, etc.)

### 2. SystemC Constructs

**Ports**:
- Inputs: `sc_in<bool>`
- Outputs: `sc_out<bool>`
- Large circuits (>500 I/O): `sc_vector<sc_in<bool>>` for bundled I/O

**Internal Signals**:
- `sc_signal<bool>` for all internal wires (no special register types)

**Processes**:
- **Combinational**: `SC_METHOD` with sensitivity on all inputs
- **Sequential**: `SC_CTHREAD` with clock edge sensitivity + `reset_signal_is()`

### 3. Verification Strategy

**Primary**: VCD-based behavioral equivalence
- Run identical testbenches on SystemC and SystemVerilog (Verilator)
- Compare VCD traces (signal-by-signal, timestep-by-timestep)
- Python script using `vcdvcd` library

**Test Vector Source**: Extract from LEAN theorem proofs
- Use proof witnesses (from `native_decide`, case analysis)
- Generate comprehensive coverage from formal verification

**Rationale**: SystemC is simulation-oriented; synthesis tools have limited support. Behavioral equivalence provides strong validation without synthesis complexity.

---

## Phase 1: Core SystemC Generator

### Critical Files

#### 1. `lean/Shoumei/Codegen/SystemC.lean` (NEW)

**Structure** (~500 lines):
```lean
namespace Shoumei.Codegen.SystemC

-- Gate type to SystemC operator mapping
def gateTypeToOperator (gt : GateType) : String

-- Wire reference (handles bundled I/O)
def wireRef (inputToIndex outputToIndex : List (Wire × Nat)) (w : Wire) : String

-- Signal declarations
def generateSignalDeclarations (c : Circuit) : String
def generatePortDeclarations (c : Circuit) (useBundledIO : Bool) : String

-- Process generation
def generateCombMethod (c : Circuit) : String
def generateSeqMethod (c : Circuit) : String

-- Constructor with sensitivity lists
def generateConstructor (c : Circuit) (isSeq : Bool) (bundled : Bool) : String

-- Main generators
def toSystemCHeader (c : Circuit) : String
def toSystemCImpl (c : Circuit) : String

end Shoumei.Codegen.SystemC
```

**Key Implementation Details**:

- **Header file** (`.h`):
  - `SC_MODULE` class definition
  - Port declarations (individual or `sc_vector`)
  - `sc_signal` declarations for internal wires
  - Process method declarations (`comb_logic()`, `seq_logic()`)
  - `SC_CTOR` with sensitivity lists

- **Implementation file** (`.cpp`):
  - `#include "ModuleName.h"`
  - `ModuleName::comb_logic()` - gate assignments in topological order
  - `ModuleName::seq_logic()` - DFF logic with `while(true) { wait(); ... }`

- **Gate operators**:
  - AND: `&`, OR: `|`, NOT: `~`, XOR: `^`
  - MUX: `sel.read() ? in1.read() : in0.read()`
  - BUF: `out.write(in.read())`
  - DFF: In `seq_logic()` with reset check

- **Large circuit support** (>500 I/O ports):
  - Use `sc_vector<sc_in<bool>> inputs;` / `sc_vector<sc_out<bool>> outputs;`
  - Constructor: `inputs("inputs", N), outputs("outputs", M)`
  - Access: `inputs[i].read()`, `outputs[j].write(val)`

---

## Phase 2: Build System Integration

### Critical Files

#### 2. `GenerateSystemC.lean` (NEW)

Entry point for SystemC code generation (~150 lines):

```lean
import Shoumei.Examples.Adder
import Shoumei.Examples.QueueExample
import Shoumei.Circuits.Combinational.RippleCarryAdderCodegen
-- ... all circuit imports

def writeSystemCFiles (c : Circuit) : IO Unit := do
  let header := Codegen.SystemC.toSystemCHeader c
  let impl := Codegen.SystemC.toSystemCImpl c

  IO.FS.writeFile s!"output/systemc/{c.name}.h" header
  IO.FS.writeFile s!"output/systemc/{c.name}.cpp" impl
  IO.println s!"✓ Generated: {c.name}.h/.cpp"

def main : IO Unit := do
  IO.println "SystemC Code Generation"

  -- Phase 0: Foundation
  writeSystemCFiles fullAdderCircuit
  writeSystemCFiles dff
  writeSystemCFiles Queue1_8
  writeSystemCFiles Queue1_32

  -- Phase 1: Arithmetic
  writeSystemCFiles mkRippleCarryAdder4
  -- ... (all 23 modules)
```

#### 3. `systemc/CMakeLists.txt` (NEW)

Build system for compiling generated SystemC (~40 lines):

```cmake
cmake_minimum_required(VERSION 3.16)
project(ShoumeiSystemC CXX)

set(CMAKE_CXX_STANDARD 17)
find_package(SystemCLanguage CONFIG REQUIRED)

file(GLOB SYSTEMC_MODULES "../output/systemc/*.cpp")

foreach(MODULE_FILE ${SYSTEMC_MODULES})
  get_filename_component(MODULE_NAME ${MODULE_FILE} NAME_WE)

  add_executable(${MODULE_NAME}_test ${MODULE_FILE})
  target_link_libraries(${MODULE_NAME}_test SystemC::systemc)
  target_include_directories(${MODULE_NAME}_test PRIVATE ../output/systemc)
endforeach()
```

#### 4. `systemc/build.sh` (NEW, executable)

```bash
#!/bin/bash
set -e

if ! pkg-config --exists systemc; then
  echo "ERROR: SystemC not found"
  echo "Install: apt-get install systemc / yay -S systemc"
  exit 1
fi

mkdir -p build
cd build
cmake ..
make -j$(nproc)
echo "✓ SystemC compilation complete"
```

---

## Phase 3: Testbench Generation with Proof Extraction

**This is the most innovative part**: Extract test vectors from LEAN theorem proofs.

### Design: Proof Witness Extraction

#### Strategy: Use Existing Semantics Functions

Call `evalCircuit` from LEAN to generate expected outputs:

```lean
def generateTestVectors (c : Circuit) : List (List Bool × List Bool) :=
  let allInputCombinations := enumerateInputs c.inputs.length
  allInputCombinations.map (fun inputs =>
    let inputEnv := mkEnv c.inputs inputs
    let outputEnv := Semantics.evalCircuit c inputEnv
    let outputs := c.outputs.map outputEnv
    (inputs, outputs)
  )
```

#### Implementation

**Create**: `lean/Shoumei/Codegen/Testbench.lean` (NEW)

```lean
namespace Shoumei.Codegen.Testbench

-- Enumerate all input combinations for small circuits
def enumerateInputs (n : Nat) : List (List Bool) :=
  if n = 0 then [[]]
  else
    let rest := enumerateInputs (n - 1)
    rest.bind (fun r => [false :: r, true :: r])

-- Generate test vectors using circuit semantics
def generateTestVectors (c : Circuit) : List (List Bool × List Bool) :=
  let allInputs := enumerateInputs c.inputs.length
  allInputs.map (fun inputs =>
    let inputEnv := mkEnv c.inputs inputs
    let outputEnv := Semantics.evalCircuit c inputEnv
    let outputs := c.outputs.map outputEnv
    (inputs, outputs)
  )

-- Generate SystemC testbench with extracted vectors
def toSystemCTestbench (c : Circuit) : String :=
  let vectors := generateTestVectors c
  generateTestbenchCode c vectors

end Shoumei.Codegen.Testbench
```

---

## Phase 4: Verification Infrastructure

### Critical Files

#### 5. `verification/vcd-equivalence.py` (NEW)

Python script for VCD comparison (~100 lines):

```python
#!/usr/bin/env python3
"""Compare VCD traces from SystemC and SystemVerilog simulations."""

import sys
from vcdvcd import VCDVCD

def compare_vcds(systemc_vcd, sv_vcd):
    vcd_sc = VCDVCD(systemc_vcd)
    vcd_sv = VCDVCD(sv_vcd)

    # Get all signals
    signals_sc = set(vcd_sc.signals.keys())
    signals_sv = set(vcd_sv.signals.keys())

    # Check signal list match
    if signals_sc != signals_sv:
        print(f"ERROR: Signal mismatch")
        return False

    # Compare all signal values
    for signal in signals_sc:
        if vcd_sc[signal].tv != vcd_sv[signal].tv:
            print(f"ERROR: Signal '{signal}' mismatch")
            return False

    return True

if __name__ == "__main__":
    if compare_vcds(sys.argv[1], sys.argv[2]):
        print("✓ VCD traces match - circuits are behaviorally equivalent")
        sys.exit(0)
    else:
        print("✗ VCD traces differ - circuits are NOT equivalent")
        sys.exit(1)
```

**Dependencies**: `pip install vcdvcd`

#### 6. `verification/run-triple-lec.sh` (NEW)

Triple equivalence checker:

```bash
#!/bin/bash
set -e

MODULE_NAME="$1"

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  Triple Equivalence Check: $MODULE_NAME"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Step 1: Structural LEC (LEAN SV ≡ Chisel SV)
echo "Step 1: LEAN SV ≡ Chisel SV (Yosys)"
./verification/run-lec.sh | grep -A5 "Module: $MODULE_NAME"

# Step 2: Run SystemVerilog simulation (Verilator)
echo "Step 2: Running SystemVerilog simulation"
mkdir -p output/vcd
verilator --cc --exe --build -Wall \
  --trace \
  output/sv-from-lean/${MODULE_NAME}.sv \
  verification/testbenches/${MODULE_NAME}_tb.cpp \
  -Mdir obj_dir/${MODULE_NAME}

./obj_dir/${MODULE_NAME}/V${MODULE_NAME}

# Step 3: Run SystemC simulation
echo "Step 3: Running SystemC simulation"
./systemc/build/bin/${MODULE_NAME}_test

# Step 4: Compare VCDs
echo "Step 4: SystemC ≡ LEAN SV (VCD comparison)"
python3 verification/vcd-equivalence.py \
  output/vcd/${MODULE_NAME}_systemc.vcd \
  output/vcd/${MODULE_NAME}_sv.vcd

echo "✓ Triple equivalence verified for $MODULE_NAME"
```

---

## Implementation Checklist

### Phase 1: Core Generator
- [ ] Create `Codegen/SystemC.lean` with gate operators and signal generation
- [ ] Implement `toSystemCHeader()` - SC_MODULE class definition
- [ ] Implement `toSystemCImpl()` - Process method implementations
- [ ] Handle combinational circuits (SC_METHOD with sensitivity)
- [ ] Handle sequential circuits (SC_CTHREAD with clock/reset)
- [ ] Support large circuits (bundled I/O with sc_vector)

### Phase 2: Build Integration
- [ ] Create `GenerateSystemC.lean` entry point
- [ ] Add `codegen_systemc` executable to `lakefile.lean`
- [ ] Create `systemc/CMakeLists.txt` for compilation
- [ ] Create `systemc/build.sh` wrapper script

### Phase 3: Testbench Generation
- [ ] Create `Codegen/Testbench.lean`
- [ ] Implement `enumerateInputs()` for exhaustive testing
- [ ] Implement `generateTestVectors()` using `evalCircuit`
- [ ] Implement `toSystemCTestbench()` with sc_main
- [ ] Add VCD trace generation

### Phase 4: Verification
- [ ] Create `verification/vcd-equivalence.py`
- [ ] Create `verification/run-triple-lec.sh`
- [ ] Update `verification/smoke-test.sh` with SystemC stages

### Phase 5: Documentation
- [ ] Update `CLAUDE.md` with SystemC backend overview
- [ ] Document installation and build commands

---

## Success Criteria

**Minimum Viable Product**:
- Generate SystemC for FullAdder (combinational)
- Generate SystemC for DFlipFlop (sequential)
- Compile with SystemC library
- Run testbench, produce VCD
- VCD comparison passes

**Full Implementation**:
- All 23 modules generate SystemC .h/.cpp/testbench
- Test vectors extracted from LEAN semantics
- CMake builds all modules
- VCD equivalence for all circuits
- Documentation complete

---

## Technical Challenges & Solutions

### Challenge 1: Test Vector Extraction
**Solution**: Use semantic evaluation via `Semantics.evalCircuit` with exhaustive enumeration for small circuits, coverage-directed for large circuits.

### Challenge 2: Sequential Circuit Testbenches
**Solution**: Testbench includes `sc_clock` signal with reset sequence generation.

### Challenge 3: VCD Signal Name Mapping
**Solution**: Normalize signal names before comparison (strip hierarchy).

### Challenge 4: SystemC Installation
**Solution**: Make SystemC backend optional - check with `pkg-config --exists systemc`.

---

## Output Directory Structure

```
/home/atv/src/Shoumei-RTL/
├── lean/Shoumei/Codegen/
│   ├── SystemC.lean          (NEW - core generator)
│   └── Testbench.lean        (NEW - testbench generation)
├── GenerateSystemC.lean      (NEW - entry point)
├── systemc/
│   ├── CMakeLists.txt        (NEW - build system)
│   ├── build.sh              (NEW - wrapper script)
│   └── build/                (generated during compilation)
├── output/
│   ├── systemc/              (NEW - generated SystemC code)
│   │   ├── *.h / *.cpp / *_tb.cpp
│   └── vcd/                  (NEW - VCD traces)
└── verification/
    ├── vcd-equivalence.py    (NEW - VCD comparison)
    └── run-triple-lec.sh     (NEW - triple verification)
```

---

## Timeline Estimate

- **Week 1**: Core generator (SystemC.lean)
- **Week 2**: Build integration (Lake, CMake)
- **Week 3**: Testbench generation with proof extraction
- **Week 4**: Verification infrastructure
- **Week 5**: Documentation and polish

---

**End of Plan**
