# SystemVerilog Assertion (SVA) Formal Property Verification

This document establishes the architecture, temporal semantics, macro guarding, and multi-backend verification flows for SystemVerilog Assertions (SVA) emitted from Shoumei's Lean 4 circuit definitions.

---

## 1. Motivation & Architecture

Formal proofs in Lean 4 establish mathematical correctness by construction (dependent type checking, inductive invariants, and bisimulation). However, translating verified circuits into synthesizable SystemVerilog introduces an semantic boundary: downstream tools (simulators, linters, ASIC synthesis, and industrial model checkers) execute on emitted RTL text.

Shoumei bridges this boundary through **SVA Formal Property Verification (FPV)**:
1. Formal properties are declared directly within circuit records in Lean (`svaProperties : List SVAProperty`).
2. The code generator (`lean/Shoumei/Codegen/SVA.lean`) translates these contracts into IEEE 1800-2017 SystemVerilog assertions, sequences, and auxiliary ghost monitors.
3. Automated runners (`verification/sva-verify.sh`) validate the properties across both open-source tools (`slang`, `verilator --assert`) and industrial formal property verification engines (Synopsys VC Formal FPV).

```
                      ┌──────────────────────────────────────┐
                      │    Lean 4 Formal Specification       │
                      │  (L0-L3 proofs, zero axioms/sorry)   │
                      └──────────────────┬───────────────────┘
                                         │ Codegen
                                         ▼
                      ┌──────────────────────────────────────┐
                      │    Emitted SystemVerilog + SVA       │
                      │     (`ifdef SHOUMEI_FORMAL_ASSERT)   │
                      └──────┬────────────────────────┬──────┘
                             │                        │
               Open-Source   │                        │ Industrial EDA
               Flow          │                        │ Flow
                             ▼                        ▼
               ┌───────────────────────┐   ┌───────────────────────────┐
               │ slang (AST/Semantics) │   │ Synopsys VC Formal (FPV)  │
               │ Verilator (--assert)  │   │  - Simon / SVAC compiler  │
               │ Dynamic C++ Monitors  │   │  - TRI / Engine Solvers   │
               └───────────────────────┘   └───────────────────────────┘
```

---

## 2. Temporal Property Semantics & Boundary Conditions

Temporal assertions reason across multiple clock cycles ($Z^{-k}$). Without explicit boundary handling, naive SVA assertions produce false counterexamples in formal tools and spurious runtime errors in simulation.

### 2.1 Multi-Cycle Flight & Reset Freedom ($Z^{-k}$)

For a pipeline register or execution unit with latency $k$:
```systemverilog
// NAIVE (Flawed):
property p_latency_naive;
  @(posedge clock) disable iff (reset)
  1'b1 |=> (q == $past(d, k));
endproperty
```
**Failure Mode:** `disable iff (reset)` only evaluates `reset` at the *current* evaluation cycle. If `reset` asserted 2 cycles ago within a $k=4$ window, the pipeline was flushed and `q` holds the reset value rather than the data in flight 4 cycles ago. The naive assertion fails falsely.

**Corrected Formulation:**
The antecedent must enforce **reset freedom across the entire transit horizon**:
```systemverilog
property p_latency_capture;
  @(posedge clock) disable iff (reset)
  (!reset [* k]) |-> (q == $past(d, k));
endproperty
assert property (p_latency_capture);
```
Here, consecutive non-reset cycles `(!reset [* k])` ensure that no asynchronous or synchronous flush corrupted the data in transit.

### 2.2 Past Validity Horizon ($past Initialization)

In both formal model checking and dynamic simulation, `$past(sig, k)` is mathematically undefined for initial cycles $t < k$.
- In simulation, evaluating uninitialized past horizons can produce `'x` mismatches.
- In formal tools (VC Formal), `create_reset -sense high` holds the design in reset during phase 0, but an unconstrained property could evaluate at cycle 1 while referencing cycle $1 - k < 0$.

**Solution:** The sequence `(!reset [* k])` inherently acts as a past-validity guard. Because `reset` was asserted at cycle 0, `(!reset [* k])` cannot match until cycle $t \ge k + 1$, guaranteeing that the past buffer contains valid, post-reset states.

### 2.3 Clock Enable Retention

For strobe-enabled registers (`RegisterEnN`), the contract separates latching from holding:
```systemverilog
// 1. Retention: Enable low preserves prior state
property p_enable_holds;
  @(posedge clock) disable iff (reset)
  !en |=> (q == $past(q));
endproperty

// 2. Capture: Enable high latches previous cycle's data
property p_enable_capture;
  @(posedge clock) disable iff (reset)
  en |=> (q == $past(d));
endproperty
```
In VC Formal, both properties converge to `proven` (non-vacuous) under multi-engine solving.

### 2.4 Decoupled Transaction Equivalence & Elastic Latency Skew

In streaming interfaces (e.g. `DecoupledSink` / `DecoupledSource`), transactions between reference and revised implementations may arrive at different cycles due to variable backpressure or pipeline bubble insertion.

Cycle-by-cycle equality `dataA == dataB` fails under elastic skew. Shoumei handles this using **auxiliary ghost transaction counters**:
```systemverilog
int unsigned ghost_enqs;
int unsigned ghost_deqs;

always_ff @(posedge clock) begin
  if (reset) begin
    ghost_enqs <= 0;
    ghost_deqs <= 0;
  end else begin
    if (enq_valid && enq_ready) ghost_enqs <= ghost_enqs + 1;
    if (deq_valid && deq_ready) ghost_deqs <= ghost_deqs + 1;
  end
end

// Exact occupancy conservation invariant:
property p_conservation;
  @(posedge clock) disable iff (reset)
  (occupancy_count == (ghost_enqs - ghost_deqs));
endproperty
```

---

## 3. Preprocessor Guarding Pattern

ASIC synthesis tools (Synopsys Design Compiler, Cadence Genus, Yosys) must never map verification assertions into silicon gates. Conversely, formal property verification tools (Synopsys VC Formal, Cadence JasperGold) must compile assertions even during formal synthesis.

Standard SystemVerilog (IEEE 1800) does not support C-style `` `if defined(...) `` expressions; it only provides `` `ifdef `` and `` `ifndef ``. Furthermore, formal tools often define `SYNTHESIS` internally.

To avoid assertion erasure in formal verification while preventing silicon overhead in ASIC builds, Shoumei uses a three-tier preprocessor guard:

```systemverilog
`ifdef FORMAL
  `define SHOUMEI_FORMAL_ASSERT
`elsif SYNTHESIS
  // Pure ASIC synthesis without FORMAL: suppress assertions
`else
  // Simulation (Verilator, VCS, Questa): active by default
  `define SHOUMEI_FORMAL_ASSERT
`endif

`ifdef SHOUMEI_FORMAL_ASSERT
  // Formal properties emitted from Lean DSL
  property p_data_capture_0;
    @(posedge clock) disable iff (reset)
    1'b1 |=> (q == $past(d));
  endproperty
  assert_data_capture_0: assert property (p_data_capture_0);
  `undef SHOUMEI_FORMAL_ASSERT
`endif
```

---

## 4. Verification Execution Flows

### 4.1 Local Open-Source Flow

Run locally via Make:
```bash
make sva
```
This executes:
1. `verification/slang-lint.py output/sv-from-lean`: Validates syntax and IEEE 1800 AST elaboration across all 230+ emitted files.
2. `verilator --assert --lint-only`: Checks that SVA properties compile into active simulation assertions.

### 4.2 Synopsys VC Formal FPV (Remote / Industrial)

Run against a compute server equipped with Synopsys VC Formal:
```bash
./verification/sva-verify.sh --remote <hostname>
```

#### Toolchain Invocations & Optimization
1. **Atomic File Transfer:** All 230+ SystemVerilog files and generated TCL scripts are piped via `tar -cf - ... | ssh ... "tar -xf - ..."` in < 1.5 seconds, bypassing `scp` command-line expansion limits.
2. **Environment Scoping:** In non-interactive SSH sessions, remote shell startup files (`.profile`, `.bashrc`, or `.zshrc`) must be sourced without subshell isolation (`{ [ -f ~/.profile ] && source ~/.profile; }`) so license environment variables persist into the parent process.
3. **Compiler Unification:** Standalone `VCS_HOME` and `VERDI_HOME` environment variables are unset so `vcf` invokes its own bundled Simon/SVAC front-end.
4. **FPV Script Execution:**
```tcl
set_fml_appmode FPV
read_file -format sverilog -vcs { +define+FORMAL Register64.sv Register32.sv Register160.sv }
elaborate -sva Register160
create_clock -period 10 clock
create_reset reset -sense high
check_fv
report_fv -list
exit
```

---

## 5. Verification Matrix & Results

| Module | Property ID | Type | Temporal Horizon | VC Formal Result | Slang / Verilator |
|---|---|---|---|---|---|
| `Register160` | `assert_data_capture_1` | L1 Functional | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `Register160` | `reg_0_to_63.assert_data_capture_1` | Compositional | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `Register160` | `reg_64_to_127.assert_data_capture_1` | Compositional | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `Register160` | `reg_128_to_159.assert_data_capture_1` | Compositional | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `RegisterEn64` | `assert_enable_capture_2` | Strobe Data | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `RegisterEn64` | `assert_enable_holds_1` | Strobe Hold | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `Register160_sec_miter` | `assert_sec_equiv_q_0` | SEC Equivalence | $\forall t \ge 1$ | **PROVEN** (non-vacuous) | Active |
