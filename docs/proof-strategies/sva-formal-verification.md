# SystemVerilog assertion (SVA) formal property verification

This document covers SystemVerilog Assertions (SVA) emitted from Shoumei's Lean 4 circuit definitions. It establishes the architecture, temporal semantics, macro guarding, and multi-backend verification flows.

---

## 1. Motivation and architecture

Formal proofs in Lean 4 establish mathematical correctness by construction (dependent type checking, inductive invariants, and bisimulation). However, translating verified circuits into synthesizable SystemVerilog introduces a semantic boundary. Downstream tools (simulators, linters, ASIC synthesis, and industrial model checkers) execute on emitted RTL text.

Shoumei bridges this boundary through **SVA Formal Property Verification (FPV)**.
1. Circuit records in Lean declare the formal properties directly (`svaProperties : List SVAProperty`).
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

## 2. Temporal property semantics and boundary conditions

Temporal assertions reason across multiple clock cycles ($Z^{-k}$). Without explicit boundary handling, naive SVA assertions produce false counterexamples in formal tools and spurious runtime errors in simulation.

### 2.1 Multi-cycle flight and reset freedom ($Z^{-k}$)

For a pipeline register or execution unit with latency $k$:
```systemverilog
// NAIVE (Flawed):
property p_latency_naive;
  @(posedge clock) disable iff (reset)
  1'b1 |=> (q == $past(d, k));
endproperty
```
**Failure mode:** `disable iff (reset)` only evaluates `reset` at the *current* evaluation cycle. Suppose `reset` asserted 2 cycles ago within a $k=4$ window. The pipeline has already flushed, so `q` holds the reset value rather than the data in flight 4 cycles ago. The naive assertion fails falsely.

**Corrected formulation:**
The antecedent must enforce **reset freedom across the entire transit horizon**:
```systemverilog
property p_latency_capture;
  @(posedge clock) disable iff (reset)
  (!reset [* k]) |-> (q == $past(d, k));
endproperty
assert property (p_latency_capture);
```
Here, consecutive non-reset cycles `(!reset [* k])` ensure that no asynchronous or synchronous flush corrupted the data in transit.

### 2.2 Past validity horizon ($past initialization)

In both formal model checking and dynamic simulation, `$past(sig, k)` has no defined value for initial cycles $t < k$.
- In simulation, evaluating uninitialized past horizons can produce `'x` mismatches.
- In formal tools (VC Formal), `create_reset -sense high` holds the design in reset. That hold spans phase 0. An unconstrained property could evaluate at cycle 1 while referencing cycle $1 - k < 0$.

**Solution:** The sequence `(!reset [* k])` inherently acts as a past-validity guard. Because the design asserts `reset` at cycle 0, `(!reset [* k])` cannot match until cycle $t \ge k + 1$. This guard guarantees that the past buffer contains valid, post-reset states.

### 2.3 Clock enable retention

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

### 2.4 Decoupled transaction equivalence and elastic latency skew

In streaming interfaces (for example, `DecoupledSink` / `DecoupledSource`), transactions between reference and revised implementations may arrive at different cycles. Variable backpressure or pipeline bubble insertion causes this skew.

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

## 3. Preprocessor guarding pattern

ASIC synthesis tools (Synopsys Design Compiler, Cadence Genus, Yosys) must never map verification assertions into silicon gates. Conversely, formal property verification tools (Synopsys VC Formal, Cadence JasperGold) must compile assertions even during formal synthesis.

Standard SystemVerilog (IEEE 1800) does not support C-style `` `if defined(...) `` expressions. It only provides `` `ifdef `` and `` `ifndef ``. Furthermore, formal tools often define `SYNTHESIS` internally.

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

## 4. Verification execution flows

### 4.1 Local open-source flow

Run locally through Bazel:
```bash
bazel test //verification:sva_verilator_test //verification:slang_lint_test
```
This executes:
1. `//verification:slang_lint_test`: Validates syntax and IEEE 1800 AST elaboration across all 230+ emitted files.
2. `//verification:sva_verilator_test`: Checks that SVA properties compile into active simulation assertions.

### 4.2 Synopsys VC Formal FPV (remote / industrial)

Run against a compute server equipped with Synopsys VC Formal:
```bash
./verification/sva-verify.sh --remote <hostname>
```

#### Toolchain invocations and optimization
1. **Atomic file transfer:** Shoumei pipes all 230+ SystemVerilog files and generated TCL scripts through `tar -cf - ... | ssh ... "tar -xf - ..."` in < 1.5 seconds. This bypasses `scp` command-line expansion limits.
2. **Environment scoping:** In non-interactive SSH sessions, the script must source remote shell startup files (`.profile`, `.bashrc`, or `.zshrc`) without subshell isolation (`{ [ -f ~/.profile ] && source ~/.profile; }`). This keeps license environment variables in the parent process.
3. **Compiler unification:** Shoumei unsets the standalone `VCS_HOME` and `VERDI_HOME` environment variables so `vcf` invokes its own bundled Simon/SVAC front-end.
4. **FPV script execution:**
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

## 5. Verification matrix and results

| Module | Property ID | Type | Temporal Horizon | VC Formal Result | Slang / Verilator |
|---|---|---|---|---|---|
| `Register160` | `assert_data_capture_1` | L1 Functional | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `Register160` | `reg_0_to_63.assert_data_capture_1` | Compositional | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `Register160` | `reg_64_to_127.assert_data_capture_1` | Compositional | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `Register160` | `reg_128_to_159.assert_data_capture_1` | Compositional | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `RegisterEn64` | `assert_enable_capture_2` | Strobe Data | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `RegisterEn64` | `assert_enable_holds_1` | Strobe Hold | 1 cycle ($Z^{-1}$) | **PROVEN** (non-vacuous) | Active |
| `Register160_sec_miter` | `assert_sec_equiv_q_0` | SEC Equivalence | $\forall t \ge 1$ | **PROVEN** (non-vacuous) | Active |
