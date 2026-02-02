# Verification Guide

How equivalence checking works in Shoumei RTL, including direct LEC, compositional verification, and troubleshooting.

## Verification Architecture

The verification pipeline has two complementary methods:

1. **Direct LEC** -- Yosys compares Lean SV vs Chisel SV at the gate level
2. **Compositional Verification** -- Lean proofs + verified building blocks

Both feed into the same script (`verification/run-lec.sh`) which reports unified coverage.

```
                         run-lec.sh
                             |
              +--------------+--------------+
              |                             |
        Direct LEC                   Compositional
    (Yosys SAT/induction)         (Lean certificates)
              |                             |
    +---------+---------+          +--------+--------+
    |                   |          |                 |
Combinational      Sequential   Check deps       Lean proof
  (CEC)              (SEC)      all verified     reference
    |                   |          |
  miter +          equiv_make +   dependency
  SAT solve        equiv_induct   verification
```

## Direct LEC

### How it works

The LEC script reads both SV files, builds an equivalence circuit, and uses a SAT solver to prove they produce identical outputs for all inputs.

### Combinational Equivalence Checking (CEC)

For circuits without registers (no `always @` blocks):

```
read_verilog -sv <lean SV>          # Read gold (Lean) design
hierarchy -check -top <module>
proc; opt; memory; opt; flatten
rename <module> gold

read_verilog -sv <chisel SV>        # Read gate (Chisel) design
hierarchy -check -top <module>
proc; opt; memory; opt; flatten
rename <module> gate

miter -equiv -flatten gold gate miter   # Build miter circuit
sat -verify -prove-asserts miter        # SAT solve
```

**Success:** `SAT proof finished - no model found: SUCCESS`
**Failure:** SAT finds a counterexample (input values where outputs differ)

### Sequential Equivalence Checking (SEC)

For circuits with registers (`always @` blocks detected):

```
# Same read + flatten steps, then:
equiv_make gold gate equiv      # Build equivalence circuit
prep -top equiv
async2sync

equiv_simple -undef             # Structural optimization
equiv_induct -undef             # Induction proof
equiv_status -assert            # Assert all equivalences hold
```

For hierarchical sequential circuits, a bounded induction depth is used:
```
equiv_induct -undef -seq 3      # 3-step induction
```

**Success:** `Equivalence successfully proven`
**Failure:** Unproven equivalence points remain

## Compositional Verification

### When to use

Use compositional verification when direct LEC fails or is impractical:

- **Structural mismatch:** Lean generates register arrays differently from Chisel
- **Large state space:** Too many registers for induction to converge
- **Hierarchical modules:** Built from verified submodules with known behavior

### How it works

1. All leaf submodules are verified by direct LEC (CEC or SEC)
2. A Lean proof establishes that the composition of verified submodules implements the specified behavior
3. A `CompositionalCert` in Lean declares the module, its dependencies, and the proof reference
4. The LEC script loads certificates, verifies all dependencies are already proven, and accepts the compositional result

### Certificate structure

Defined in `lean/Shoumei/Verification/Compositional.lean`:

```lean
structure CompositionalCert where
  moduleName : String              -- Module being verified
  dependencies : List String       -- Submodules that must be LEC-verified first
  proofReference : String          -- Lean namespace containing the composition proof
```

### Certificate registry

All certificates live in `lean/Shoumei/Verification/CompositionalCerts.lean`:

```lean
def register91_cert : CompositionalCert := {
  moduleName := "Register91"
  dependencies := ["Register64", "Register16", "Register8", "Register2", "Register1"]
  proofReference := "Shoumei.Circuits.Sequential.RegisterProofs"
}

def allCerts : List CompositionalCert := [
  register91_cert,
  queue64_32_cert,
  ...
]
```

### Export mechanism

`ExportVerificationCerts.lean` exports certificates in `module|dep1,dep2,...|proof_ref` format:

```bash
$ lake exe export_verification_certs
Register91|Register64,Register16,Register8,Register2,Register1|Shoumei.Circuits.Sequential.RegisterProofs
Queue64_32|QueueRAM_64x32,QueuePointer_6,QueueCounterUpDown_7|Shoumei.Circuits.Sequential.QueueProofs
...
```

The LEC script calls this and parses the output into a bash associative array.

### Current compositional modules

| Module | Dependencies | Proof |
|--------|-------------|-------|
| Register91 | Register64, Register16, Register8, Register2, Register1 | RegisterProofs |
| Queue64_32 | QueueRAM_64x32, QueuePointer_6, QueueCounterUpDown_7 | QueueProofs |
| Queue64_6 | QueueRAM_64x6, QueuePointer_6, QueueCounterUpDown_7 | QueueProofs |
| QueueRAM_64x32 | Register32, Decoder6, Mux64x32 | QueueProofs |
| QueueRAM_64x6 | Register6, Decoder6, Mux64x6 | QueueProofs |
| PhysRegFile_64x32 | Decoder6, Mux64x32 | PhysRegFileProofs |
| RAT_32x6 | Decoder5, Mux32x6 | RATProofs |
| FreeList_64 | QueueRAM_64x6, QueuePointer_6, QueueCounterUpDown_7, Decoder6, Mux64x6 | FreeListProofs |
| ReservationStation4 | Register2, Register91, Comparator6, Mux4x6, Mux4x32, Decoder2, PriorityArbiter4 | ReservationStationProofs |

## Topological Sorting

The LEC script processes modules in dependency order. This is critical because compositional certificates require all dependencies to be verified first.

### How it works

1. Build a dependency graph from compositional certificates
2. Pipe through `awk` to generate `tsort`-compatible pairs
3. `tsort` produces a topological ordering
4. Modules without dependencies come first, then dependent modules

Example ordering:
```
Register1          # No dependencies, verified first
Register2
Register8
Register16
Register64
Register91         # Depends on Register{1,2,8,16,64}
Decoder6
Mux64x32
QueuePointer_6
QueueCounterUpDown_7
QueueRAM_64x32     # Depends on Register32, Decoder6, Mux64x32
Queue64_32         # Depends on QueueRAM_64x32, QueuePointer_6, QueueCounterUpDown_7
```

## Chisel Cleaning

Before LEC, Chisel output is cleaned for Yosys compatibility:

1. **Remove CIRCT verification blocks:** Everything after `// ----- 8< -----`
2. **Convert automatic variables:** `automatic logic x = y;` -> `logic x; x = y;`
3. **Remove `automatic` keyword:** Yosys doesn't support it

This happens automatically in `run-lec.sh` and writes to a temp directory.

## Troubleshooting

### LEC says "VERIFICATION INCOMPLETE"

**Possible causes:**
- Yosys couldn't read one of the SV files (syntax error)
- Induction didn't converge (increase depth or use compositional)
- Port name mismatch between Lean and Chisel output

**Debug steps:**
1. Check the Yosys output (last 20 lines are printed)
2. Try reading each SV file individually:
   ```bash
   yosys -p "read_verilog -sv output/sv-from-lean/MyModule.sv"
   yosys -p "read_verilog -sv output/sv-from-chisel/MyModule.sv"
   ```
3. Compare port lists:
   ```bash
   grep "input\|output" output/sv-from-lean/MyModule.sv
   grep "input\|output" output/sv-from-chisel/MyModule.sv
   ```

### LEC says "NOT EQUIVALENT"

**This means the two generators produce different logic.** This is a real bug.

**Debug steps:**
1. The SAT solver found a counterexample -- check the failing assertions
2. Diff the two SV files to find structural differences
3. Common causes:
   - Off-by-one in wire indexing
   - Different reset behavior
   - Missing or extra gates in one generator
   - Clock/reset handling differences (check `findClockWires`/`findResetWires`)

### Compositional verification says "INCOMPLETE"

**Means one or more dependencies aren't verified yet.**

**Debug steps:**
1. Check which dependencies are missing (printed in output)
2. Ensure the dependency modules exist in both `output/sv-from-lean/` and `output/sv-from-chisel/`
3. Verify the dependency modules pass LEC individually
4. Check topological ordering -- the dependency should come before the dependent module

### Chisel compilation fails before LEC

See the "Common Chisel compilation issues" table in [docs/adding-a-module.md](adding-a-module.md).

The most common issue is `IndexOutOfBoundsException` from incorrect input indexing, caused by clock/reset not being filtered. Fix: ensure `findClockWires` and `findResetWires` in `Common.lean` detect your module's clock/reset wires (from both DFF gates and instance connections).

## Running Verification

### Full LEC (all modules)

```bash
./verification/run-lec.sh
```

### Smoke test (CI pipeline)

```bash
./verification/smoke-test.sh
```

Tests: Lean build, formal proofs, code generation, Chisel compilation, port validation, LEC.

### Via Make

```bash
make lec              # Just LEC
make verify           # LEC + EQY
make smoke-test       # Full CI pipeline
make all              # Build + codegen + chisel + LEC
```

## Adding a New Compositional Certificate

1. Verify all building blocks pass direct LEC
2. Write the composition proof in Lean (or reference existing proofs)
3. Add `CompositionalCert` to `CompositionalCerts.lean`
4. Add to `allCerts` list
5. Run `lake build` to ensure it compiles
6. Run `./verification/run-lec.sh` to see the module verified compositionally
