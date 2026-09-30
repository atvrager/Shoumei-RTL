# Proof strategy: register refinement and temporal invariants

This document details the first-principles proof architecture for sequential register circuits in Shoumei (`mkRegisterN` and `mkRegisterNHierarchical`). It links cycle-by-cycle behavioral, inductive, and temporal verification directly to synthesizable SystemVerilog Assertions (SVA).

---

## 1. Physical intuition and formal framing

In hardware, an $N$-bit register that stores $N$ data bits contains exactly $N$ parallel flip-flops.
- $N \times \text{DFF}$ instances clocked by a common `clock` and reset by a common synchronous `reset`.
- Physically, the state space has at most $2^N$ states.

However, in the Lean DSL, the hardware state is an open environment.
```lean
abbrev State := Wire → Bool
```
Because `Wire → Bool` is an infinite mathematical function, automated provers cannot evaluate all possible states without bounding.

---

## 2. The solution: state projection (relevant support)

To bridge the gap between infinite mathematical functions and finite physical flip-flops:

1. **DFF output extraction**:
   The sequential evaluator `evalCycleSequential` only reads from and writes to flip-flop outputs defined by `getDFFOutputs(C)`. For `mkRegisterN`, this set is strictly:
   $$\text{supp}(C) = \{\text{"q\_0"}, \text{"q\_1"}, \dots, \text{"q\_(N-1)"}\}$$

2. **Canonical state projection**:
   Canonical state and environment projectors map finite boolean tuples to the exact circuit flip-flops and inputs:
   ```lean
   def reg1CanonicalState (q0 : Bool) : State :=
     fun w => if w == Wire.mk "q_0" then q0 else false

   def reg1InputEnv (d0 clock reset : Bool) : Env :=
     fun w =>
       if w == Wire.mk "d_0" then d0
       else if w == Wire.mk "clock" then clock
       else if w == Wire.mk "reset" then reset
       else false
   ```

3. **Universe invariance**:
   `mergeStateIntoEnv` ignores any wire outside $\text{supp}(C)$. The functional domain collapses to finite boolean combinations, enabling deterministic decision procedures (`native_decide`) for leaf widths.

---

## 3. The register behavioral invariants

### Invariant 1: synchronous reset zeroing
The design asserts reset at cycle $t$. Every output bit $q_i$ must evaluate to false at cycle $t+1$. This holds regardless of prior register state or input data.
$$\forall t, \quad \text{reset}_t = \text{true} \implies q_{t+1}[i] = \text{false}$$

### Invariant 2: active clock data capture
The design deasserts reset at cycle $t$. Every output bit $q_i$ captures the corresponding input $d_i$:
$$\forall t, \quad \text{reset}_t = \text{false} \implies q_{t+1}[i] = d_t[i]$$

---

## 4. Factored scaling: bit-slice independence

A naive 64-bit register truth table needs $2^{64 \text{ state} + 64 \text{ data} + 2 \text{ ctrl}} = 2^{130}$ combinations. That count is impossible to compute.

### The bit-slice decomposition
1. **Gate independence**:
   `mkRegisterN` consists solely of $N$ disjoint DFF gates:
   $$\text{gate}_i = \text{Gate.mkDFF } d_i \text{ clock reset } q_i$$
2. **Combinational passthrough**:
   `mkRegisterN` contains zero combinational gates (`register_all_gates_are_dff`). Combinational fixed-point settling is the identity function.
3. **Orthogonal state updates**:
   Bit $i$ depends exclusively on $(d_i, \text{clock}, \text{reset})$. Changes on $d_j$ ($j \ne i$) cannot propagate to $q_i$.
   This reduces an exponential $2^{2N+2}$ state explosion to $O(N)$ independent proofs.

---

## 5. Hierarchical composition for large pipeline registers

Shoumei builds large pipeline registers (`Register91`, `Register96`, `Register98`, `Register130`, `Register157`, `Register158`, `Register159`, `Register160`) hierarchically from power-of-2 building blocks (`Register64`, `Register32`, and others).

The proof establishes formal composition rather than instance counts.
1. **Complete bit coverage**:
   Every bit index $k \in [0, N-1]$ maps to exactly one child instance port.
   ```lean
   theorem register96_outputs_cover_all_bits :
     (mkRegister96Hierarchical.instances.flatMap instanceOutputWires == makeIndexedWires "q" 96) = true := by native_decide
   theorem register96_inputs_cover_all_bits :
     (mkRegister96Hierarchical.instances.flatMap instanceInputWires == makeIndexedWires "d" 96) = true := by native_decide
   ```
2. **Clock and reset distribution**:
   Every child subcircuit connects strictly to the top-level `clock` and `reset` nets.
   ```lean
   theorem register96_clock_synchronized : ... = true := by native_decide
   theorem register96_reset_synchronized : ... = true := by native_decide
   ```
3. **Refinement preservation**:
   The proof uses `dual_compositional_refinement`. Slice $[0, 63]$ and slice $[64, 95]$ satisfy their register specifications. The composite circuit then satisfies the full 96-bit specification.

---

## 6. Real linkage to SystemVerilog AST (SVA)

Proven Lean properties are not isolated mathematical lemmas. The tool embeds them directly into the circuit definition and emits them into the SystemVerilog AST:

```lean
svaProperties := [
  .ResetClears "q",
  .DataCapture "d" "q"
]
```

When emitted by `Unified.lean` / `SystemVerilog.lean`, the resulting RTL contains synthesizable assertions guarded under `` `ifndef SYNTHESIS ``:

```systemverilog
`ifndef SYNTHESIS
  // Formal Property: Synchronous reset clears register
  property p_reset_clears_0;
    @(posedge clock) reset |=> (q == '0);
  endproperty
  assert_reset_clears_0: assert property (p_reset_clears_0);

  // Formal Property: Active clock edge latches data
  property p_data_capture_1;
    @(posedge clock) disable iff (reset)
    1'b1 |=> (q == $past(d));
  endproperty
  assert_data_capture_1: assert property (p_data_capture_1);
`endif
```

These assertions are:
- Elaborated and type-checked by `slang` (IEEE 1800-2017).
- Verified during cycle-accurate Verilator simulation.
- Usable directly in formal property checking tools (SymbiYosys, JasperGold).

---

## 7. Strict bit-slice non-interference (information flow security)

In secure hardware architectures, register slices must guarantee complete cross-lane isolation.
- **Functional non-interference (`register_slice_non_interference`)**: The single-step evaluation of slice $i$ depends only on $d_i$, clock, and reset. Changing any input wire $d_j$ ($j \neq i$) produces zero change on $q_i$.
- **Trace non-interference (`register_slice_trace_non_interference`)**: Two independent execution traces $tr_1$ and $tr_2$ may agree on bit $i$ at cycle $t$. Their next-cycle outputs on bit $i$ are identical, regardless of all other $N-1$ data lanes.
- **Reset isolation (`register_slice_trace_reset_isolation`)**: Under synchronous reset, the cleared state of slice $i$ is false across all traces.

---

## 8. Multi-cycle pipeline latency ($Z^{-k}$ delay functor)

Chaining sequential registers forms discrete-time delay lines.
- **2-stage delay ($Z^{-2}$)**: Theorem `register_pipeline_2stage_delay` proves that over consecutive active cycles $t$ and $t+1$ without reset, $Q[t+2] = D[t]$.
- **3-stage delay ($Z^{-3}$)**: Theorem `register_pipeline_3stage_delay` proves $Q[t+3] = D[t]$ across 3 active stages.
- **Reset propagation**: Theorem `register_pipeline_reset_propagation` proves reset behavior. Asserting reset at cycle $t$ clears stage 1 at $t+1$ and flushes zero into stage 2 at $t+2$.

---

## 9. Clock-enabled registers (`mkRegisterEnN` and strobe refinement)

This section covers pipeline stall logic, clock gating, and retention registers.
1. **Structural MUX refinement**:
   Each bit pairs a 2-to-1 MUX and a DFF.
   $$\text{next\_d}_i = \text{en} \,?\, d_i : q_i, \quad q_i \gets \text{DFF}(\text{next\_d}_i)$$
   Theorems `evalMUX_enable_false_selects_q` and `evalMUX_enable_true_selects_d` prove that the MUX implements the retention and update functions.
2. **L1 cycle truth**:
   Exhaustively proven for 1-bit (`registerEn1`) and 2-bit (`registerEn2`):
   - `registerEn1_functional_reset_zeroes`: Reset clears output to false regardless of enable.
   - `registerEn1_functional_enable_holds`: `en = false` holds prior state $q_0$.
   - `registerEn1_functional_enable_latches`: `en = true` captures input $d_0$.
3. **SVA emission**:
   Generates bus-level assertions for clock enable:
   - `assert_enable_holds`: `!en |=> (q == $past(q))`
   - `assert_enable_capture`: `en |=> (q == $past(d))`

---

## 10. Sequential equivalence checking (SEC bisimulation)

This section guarantees that hierarchical decomposition introduces zero behavioral divergence.
- **I/O congruence**: Theorems `register*_sec_inputs_identical` and `register*_sec_outputs_identical` verify bit-for-bit identity between `mkRegisterN` and `mkRegisterNHierarchical` port lists. This holds across all widths (91, 96, 98, 130, 157, 158, 159, 160).
- **Trace bisimulation**: Theorem `register_hierarchical_bisim_flat` formally equates the trace contracts:
  $$\text{CircuitTrace}(\text{mkRegisterNHierarchical } n) \iff \text{CircuitTrace}(\text{mkRegisterN } n)$$
This allows downstream proofs to substitute hierarchical composite registers with flat arrays transparently.
