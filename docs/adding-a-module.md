# Adding a New Module

Step-by-step guide for building a new verified circuit in Shoumei RTL. This covers the full lifecycle from behavioral model to LEC verification.

## Overview

Every module follows this pipeline:

```
Behavioral Model -> Structural Circuit -> Proofs -> Codegen -> Chisel Compile -> LEC
```

The behavioral model is optional for simple combinational circuits, but required for anything with state (sequential circuits, RISC-V components).

## Step 1: Behavioral Model

Define the state and operations in pure Lean. This is the "specification" that proofs verify against.

**File location:** Same directory as the structural circuit (e.g., `lean/Shoumei/Circuits/Sequential/MyModule.lean`)

### Example: A simple counter

```lean
-- Behavioral model: what the counter should do
structure CounterState (width : Nat) where
  value : Fin (2^width)

def CounterState.increment (s : CounterState w) : CounterState w :=
  { value := ⟨(s.value.val + 1) % (2^w), Nat.mod_lt _ (Nat.pos_of_ne_zero (by omega))⟩ }

def CounterState.reset : CounterState w :=
  { value := ⟨0, by omega⟩ }
```

### Patterns to follow

| Pattern | Example File | What it demonstrates |
|---------|-------------|---------------------|
| Register state | `Circuits/Sequential/Register.lean` | Simple parallel DFF array |
| Queue state | `Circuits/Sequential/Queue.lean` | State transitions, FIFO ordering |
| Circular buffer | `Circuits/Sequential/QueueN.lean` | Head/tail pointers, wraparound |
| Register file | `RISCV/Renaming/PhysRegFile.lean` | Read/write with Fin indexing |
| Rename mapping | `RISCV/Renaming/RAT.lean` | Lookup/allocate operations |

## Step 2: Structural Circuit

Build the actual hardware circuit using the DSL types from `DSL.lean`.

### Small combinational circuits: Direct gate list

```lean
def mkMyAdder : Circuit :=
  let a := Wire.mk "a"
  let b := Wire.mk "b"
  let sum := Wire.mk "sum"
  let carry := Wire.mk "carry"
  let ab_xor := Wire.mk "ab_xor"
  { name := "MyAdder"
    inputs := [a, b]
    outputs := [sum, carry]
    gates := [
      Gate.mkXOR a b ab_xor,
      -- ... more gates
    ]
    instances := [] }
```

### Large or sequential circuits: Hierarchical instances

For circuits with registers, or circuits large enough that direct SEC would fail, use `CircuitInstance` to reference verified building blocks:

```lean
def mkMyModule : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  -- ... define wires ...
  { name := "MyModule"
    inputs := [clock, reset, ...]
    outputs := [...]
    gates := [
      -- Glue logic only (muxing, AND/OR for control signals)
      Gate.mkAND valid_in enable write_en,
      ...
    ]
    instances := [
      -- Reference verified submodules
      { moduleName := "Register32"
        instName := "u_data_reg"
        portMap := [
          ("clock", clock), ("reset", reset),
          ("d0", data_in_0), ("d1", data_in_1), ...
          ("q0", data_out_0), ("q1", data_out_1), ...
        ] },
      { moduleName := "Decoder5"
        instName := "u_write_dec"
        portMap := [
          ("in0", addr_0), ("in1", addr_1), ...
          ("out0", sel_0), ("out1", sel_1), ...
        ] },
    ] }
```

### Port mapping conventions

- Clock and reset wires: named `"clock"` and `"reset"` -- codegen filters these for Chisel (implicit ports)
- Instance port names must match the target module's port names exactly
- Use consistent naming: `u_` prefix for instance names, numbered suffixes for arrays

### Available building blocks

All of these are LEC-verified and ready to use as instances:

| Module | Purpose | Key ports |
|--------|---------|-----------|
| `RegisterN` (1-64) | N-bit register | clock, reset, d0..dN, q0..qN |
| `Register91` | Hierarchical 91-bit reg | (composed of Register64+16+8+2+1) |
| `DecoderN` (1-6) | N-to-2^N one-hot | in0..inN, out0..out2^N |
| `MuxMxN` | M:1 mux, N bits wide | inputs, sel, out |
| `ComparatorN` | N-bit comparison | a, b, eq/lt/ltu/gt/gtu |
| `PriorityArbiterN` | N-input arbiter | request0..N, grant0..N, valid |
| `QueueRAM_DxW` | RAM for queue storage | clock, reset, read/write ports |
| `QueuePointer_N` | Queue head/tail pointer | clock, reset, en, count bits |
| `QueueCounterUpDown_N` | Up/down counter | clock, reset, up, down, count bits |

### When to use hierarchical vs flat

- **Flat (gates only):** Combinational circuits under ~500 gates. Direct LEC works.
- **Hierarchical (instances):** Sequential circuits, anything with registers, anything over ~1000 gates, or anything where Lean SV and Chisel SV would differ structurally.

## Step 3: Proofs

Create a separate proofs file. Convention: `MyModuleProofs.lean` next to `MyModule.lean`.

### Structural proofs

These verify the circuit was constructed correctly:

```lean
import Shoumei.Circuits.Sequential.MyModule

namespace Shoumei.Circuits.Sequential.MyModuleProofs

-- Gate count
theorem myModule_gate_count : mkMyModule.gates.length = 42 := by native_decide

-- Port counts
theorem myModule_input_count : mkMyModule.inputs.length = 10 := by native_decide
theorem myModule_output_count : mkMyModule.outputs.length = 8 := by native_decide

-- Instance count (for hierarchical circuits)
theorem myModule_instance_count : mkMyModule.instances.length = 3 := by native_decide

-- Module name
theorem myModule_name : mkMyModule.name = "MyModule" := by native_decide

end Shoumei.Circuits.Sequential.MyModuleProofs
```

### Behavioral proofs

These verify the state machine does what the behavioral model says:

```lean
-- Concrete proofs (small state spaces) -- use native_decide
theorem counter4_reset : (CounterState.reset : CounterState 4).value = 0 := by native_decide

-- Generic proofs (all sizes) -- use simp + manual tactics
theorem prf_read_after_write (state : PhysRegFileState n) (tag : Fin n) (val : UInt32) :
    (state.write tag val).read tag = val := by
  simp [PhysRegFileState.write, PhysRegFileState.read]
```

### Common proof techniques

| Technique | When to use | Example |
|-----------|-------------|---------|
| `native_decide` | Concrete, decidable propositions | Gate counts, small-state behavioral |
| `simp [defs...]` | Unfolding definitions | Read-after-write, init state |
| `omega` | Linear arithmetic on Nat/Int | Queue pointer wraparound |
| `bv_decide` | BitVec arithmetic (with bridge) | ALU correctness |
| Axiom + TODO | Complex proofs deferred | Mark with clear comment |

## Step 4: Code Generation

### Option A: Centralized (recommended)

Add your circuit to `GenerateAll.lean`:

```lean
-- In the allCircuits list:
def allCircuits : List Circuit := [
  ...existing modules...
  mkMyModule,
]
```

Then run:
```bash
lake exe generate_all
```

This generates all 4 outputs in one command:
- SystemVerilog (hierarchical): `output/sv-from-lean/`
- SystemVerilog netlist (flat): `output/sv-netlist/`
- Chisel → SV via CIRCT: `chisel/src/main/scala/generated/`
- SystemC: `output/systemc/`

### Option B: Dedicated codegen file

For circuits that need special codegen handling (e.g., RISC-V decoder with custom SV generation), create a `MyModuleCodegen.lean`:

```lean
import Shoumei.Circuits.Sequential.MyModule
import Shoumei.Codegen.SystemVerilog
import Shoumei.Codegen.Chisel

def main : IO Unit := do
  let c := mkMyModule
  IO.FS.writeFile "output/sv-from-lean/MyModule.sv" (generateSystemVerilog c)
  IO.FS.writeFile "chisel/src/main/scala/generated/MyModule.scala" (generateChisel c)
```

Add a Lake target in `lakefile.lean`:
```lean
lean_exe generate_mymodule where
  root := `GenerateMyModule
  supportInterpreter := true
```

## Step 5: Chisel Compilation

```bash
cd chisel && sbt run
```

`Main.scala` auto-discovers all `.scala` files in `src/main/scala/generated/` and compiles them to SystemVerilog via CIRCT. Output goes to `output/sv-from-chisel/`.

### Common Chisel compilation issues

| Error | Cause | Fix |
|-------|-------|-----|
| `IndexOutOfBoundsException` | Clock/reset not filtered from inputs | Ensure `findClockWires`/`findResetWires` detect your module's clock/reset |
| `not fully initialized` | Missing gate type in codegen | Add case to `generateCombGateIndexed` in `Chisel.lean` |
| JVM bytecode limit | Module too large (>64KB method) | Use wire arrays (`Vec`) and chunked initialization |

## Step 6: LEC Verification

```bash
./verification/run-lec.sh
```

The script:
1. Loads compositional certificates from Lean
2. Sorts modules in topological (dependency) order
3. For each module:
   - If it has a compositional cert and all deps are verified: accepts compositional proof
   - If sequential: uses `equiv_make` + `equiv_induct` (SEC)
   - If combinational: uses `miter` + `sat` (CEC)

### If LEC fails

1. Check Yosys output in the temp directory (script prints last 20 lines)
2. Common causes:
   - Port name mismatch between Lean SV and Chisel SV
   - Structural differences in sequential logic (consider compositional verification)
   - Missing module in Chisel output (check `sbt run` succeeded)
3. Compare the two SV files manually: `diff output/sv-from-lean/MyModule.sv output/sv-from-chisel/MyModule.sv`

## Step 7: Compositional Certificate (if needed)

If direct LEC fails for a hierarchical module (common for large sequential circuits):

### 1. Add certificate to `lean/Shoumei/Verification/CompositionalCerts.lean`

```lean
def myModule_cert : CompositionalCert := {
  moduleName := "MyModule"
  dependencies := ["Register32", "Decoder5", "Mux4x8"]
  proofReference := "Shoumei.Circuits.Sequential.MyModuleProofs"
}
```

Add it to `allCerts`:
```lean
def allCerts : List CompositionalCert := [
  ...existing certs...
  myModule_cert,
]
```

### 2. Update the export executable

In `ExportVerificationCerts.lean`, ensure `allCerts` is imported (usually automatic since it references the same list).

### 3. Verify

```bash
lake build
./verification/run-lec.sh
```

The module should now show as "COMPOSITIONALLY VERIFIED" instead of running direct LEC.

## Complete Example: Adding a 4-bit Counter

```
lean/Shoumei/Circuits/Sequential/Counter.lean      # Behavioral + structural
lean/Shoumei/Circuits/Sequential/CounterProofs.lean # Proofs
```

1. Define behavioral model (CounterState with increment/reset)
2. Build structural circuit using Register4 instance + increment logic gates
3. Prove structural properties (gate count, port count)
4. Prove behavioral properties (reset sets to 0, increment wraps correctly)
5. Add to `GenerateAll.lean` circuit list
6. Run `lake exe generate_all`
7. Run `cd chisel && sbt run`
8. Run `./verification/run-lec.sh`
9. If LEC fails: add compositional certificate
