# Proof strategy: queue refinement and temporal invariants

This document details the first-principles proof architecture for sequential queue circuits in Shoumei. It covers cycle-by-cycle behavioral and temporal verification, not gate and port counts.

---

## 1. Physical intuition and formal framing

In hardware, a single-entry queue (`Queue1`) storing $W$ data bits contains exactly $W + 1$ flip-flops:
- $1 \times \text{DFF}$ for the `valid` flag.
- $W \times \text{DFFs}$ for the `data_reg` bits.

Physically, the state space has at most $2^{W+1}$ states.

However, in the Lean DSL, the hardware state is an open environment.
```lean
abbrev State := Wire → Bool
```
Because `Wire → Bool` has an unbounded domain of wire names, Lean's automated provers cannot search or evaluate all possible states.

---

## 2. The solution: state projection (relevant support)

To bridge the gap between infinite mathematical functions and finite physical flip-flops:

1. **DFF output extraction**: the sequential evaluator `evalCycleSequential` only writes to and reads from flip-flop outputs defined by `getDFFOutputs(C)`. For `Queue1`, this set is strictly:
   $$\text{supp}(C) = \{\text{"valid"}, \text{"data\_reg\_0"}, \dots, \text{"data\_reg\_(W-1)"}\}$$

2. **Canonical state projection**:
   A canonical state projector maps any `State` function to its exact projection on the circuit's flip-flops:
   ```lean
   def q1w1CanonicalState (valid : Bool) (data0 : Bool) : State :=
     fun w =>
       if w == Wire.mk "valid" then valid
       else if w == Wire.mk "data_reg_0" then data0
       else false
   ```

3. **Universe invariance**:
   `mergeStateIntoEnv` ignores any wire not in $\text{supp}(C)$. The infinite functional domain collapses to a finite boolean tuple. For $W=1$, this leaves exactly $2^2 = 4$ states and $2^3 = 8$ control inputs, enabling exhaustive, deterministic decision procedures (`native_decide`).

---

## 3. The decoupled handshake stability invariant

### The invariant
A foundational rule of the AXI / Decoupled ready-valid handshake is the stability rule.
> **Stability**: Suppose the producer presents valid data at cycle $t$ and the consumer is not ready ($\text{valid} \land \neg\text{ready}$). The interface must then hold that data. It must not drop or mutate the data at cycle $t + 1$.

In temporal logic terms:
$$\forall t, \quad (\text{valid}_t \land \neg\text{ready}_t \land \neg\text{reset}_t) \implies (\text{valid}_{t+1} = \text{true} \land \text{data}_{t+1} = \text{data}_t)$$

### The gate-level proof
The circuit netlist guarantees this property as follows:
1. **Control path**:
   - $\text{deq\_fire} = \text{valid} \land \text{deq\_ready} = 1 \land 0 = 0$.
   - $\text{not\_deq\_fire} = \neg\text{deq\_fire} = 1$.
   - $\text{valid\_hold} = \text{valid} \land \text{not\_deq\_fire} = 1 \land 1 = 1$.
   - $\text{valid\_next} = \text{enq\_fire} \lor \text{valid\_hold} = \text{enq\_fire} \lor 1 = 1$.
   - When the clock ticks without reset, the valid DFF latches `valid_next = 1`.

2. **Data path**:
   - $\text{enq\_ready} = \neg\text{valid} = \neg 1 = 0$ (the queue is full, so it refuses new writes).
   - $\text{enq\_fire} = \text{enq\_valid} \land \text{enq\_ready} = \text{enq\_valid} \land 0 = 0$.
   - A MUX feeds each data bit $i$:
     $$\text{data\_next}_i = \text{MUX}(\text{data\_reg}_i, \text{enq\_data}_i, \text{enq\_fire})$$
   - Since $\text{enq\_fire} = 0$, the MUX selects $\text{data\_reg}_i$.
   - At the clock tick, the DFF latches $\text{data\_next}_i = \text{data\_reg}_i$.

Lean formally verifies this reasoning for width 1, width 2, and factored width 32 in [`lean/Shoumei/Circuits/Sequential/QueueTemporalProofs.lean`](../../lean/Shoumei/Circuits/Sequential/QueueTemporalProofs.lean).

---

## 4. Factored scaling (width 32 and beyond)

A naive truth table for a 32-bit queue would require the following evaluation count.
$$2^{\text{valid} + 32 \text{ data} + 32 \text{ enq\_data} + \text{enq\_valid} + \text{deq\_ready}} = 2^{67} \text{ combinations}$$
This is intractable for brute-force checkers.

### The factored decomposition
1. **Control path lemma**:
   The control logic depends only on 3 bits: $\text{valid}$, $\text{enq\_valid}$, and $\text{deq\_ready}$ ($2^3 = 8$ cases).
   We prove that under stall ($\text{valid} = 1, \text{deq\_ready} = 0$), $\text{valid\_next} = 1$ and $\text{enq\_fire} = 0$:
   ```lean
   theorem queue1_w32_handshake_stable_control (enq_valid : Bool) :
     valid_next = true ∧ enq_fire = false
   ```

2. **Bit-slice independence lemma**:
   Each data bit has a narrow dependency. Bit $i \in \{0, \dots, W-1\}$ depends only on $\text{enq\_fire}$, $\text{enq\_data}_i$, and $\text{data\_reg}_i$.
   Because $\text{enq\_fire} = 0$, the conditional holds.
   ```lean
   theorem queue1_data_hold_when_not_enq_fire (cur_d enq_d : Bool) :
     (if false then enq_d else cur_d) = cur_d
   ```
This reduces an exponential $2^{67}$ state explosion to $8 + 32 \times 4 = 136$ evaluations, completing in milliseconds.

---

## 5. From Lean theorem to SystemVerilog assertion (SVA)

The exact formula proven in Lean maps directly to IEEE 1800-2017 SystemVerilog Assertions:

| Lean Formulation | SystemVerilog Assertion (SVA) |
| :--- | :--- |
| `satisfiesTrace tr (.HandshakeStable "valid" "deq_ready" [data])` | `property p_stable; @(posedge clk) disable iff (reset) (valid && !deq_ready) \|=> (valid && $stable(data)); endproperty` |
| `queue1_w1_enq_ready_complement` | `assert property (@(posedge clk) enq_ready == !valid);` |
| `queue1_w1_reset_clears_valid` | `property p_rst; @(posedge clk) reset \|=> !valid; endproperty` |

This dual representation enables:
1. **Mathematical certainty in Lean**: Refinement holds over all infinite traces by structural and temporal induction.
2. **Dynamic assertion monitoring**: Verilator simulation catches any violation at runtime with zero overhead when disabled.
3. **Silicon formal signoff**: EDA tools (SymbiYosys, JasperGold, VC Formal) can consume the emitted SVA directly. They run bounded and unbounded model checking.
