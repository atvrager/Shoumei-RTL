/-
SVA-lifted properties for the emitted Queue1_8 netlist.

The models below are generated (`output/sec-bridge/`, built by `make sec-bridge`);
only the properties are authored.  Sequential equivalence against
`Queue1_spec.sv` lives in the generated `ShoumeiSec.BridgeQueue1_8.queue1_8_sec`,
so this file states only what that theorem does not: the ready/valid contract and
the two-cycle handshake and enqueue transitions that `Queue1_spec.sv` asserts in
its `SHOUMEI_FORMAL_ASSERT` block.
-/

import ShoumeiSec.Bridge.Queue1_8Spec
import ShoumeiSec.Bridge.Queue1_8Impl
import Std.Tactic.BVDecide

namespace ShoumeiSec.BridgeQueue1Properties

set_option linter.unusedVariables false

/-- Ready-Valid contract: the queue accepts an enqueue exactly when it is empty. -/
theorem enq_ready_contract
    (i : ShoumeiSec.Bridge.Queue1_8Impl.Inputs)
    (s : ShoumeiSec.Bridge.Queue1_8Impl.State) :
    (ShoumeiSec.Bridge.Queue1_8Impl.step i s).1.enq_ready =
      ~~~(ShoumeiSec.Bridge.Queue1_8Impl.step i s).1.valid := by
  obtain ⟨enq_d, enq_v, deq_r, clk, rst⟩ := i
  obtain ⟨d, v⟩ := s
  simp only [ShoumeiSec.Bridge.Queue1_8Impl.step]

/-- Handshake stability: a full, unacknowledged queue holds its data. -/
theorem handshake_stable
    (s₀ : ShoumeiSec.Bridge.Queue1_8Impl.State)
    (i₀ i₁ : ShoumeiSec.Bridge.Queue1_8Impl.Inputs)
    (h_rst0 : i₀.reset = 0#1) (h_rst1 : i₁.reset = 0#1)
    (h_valid : (ShoumeiSec.Bridge.Queue1_8Impl.step i₀ s₀).1.valid = 1#1)
    (h_not_rdy : i₀.deq_ready = 0#1) :
    let s₁ := (ShoumeiSec.Bridge.Queue1_8Impl.step i₀ s₀).2
    let o₁ := (ShoumeiSec.Bridge.Queue1_8Impl.step i₁ s₁).1
    o₁.valid = 1#1 ∧
    o₁.data_reg = (ShoumeiSec.Bridge.Queue1_8Impl.step i₀ s₀).1.data_reg := by
  obtain ⟨ed0, ev0, dr0, c0, r0⟩ := i₀
  obtain ⟨ed1, ev1, dr1, c1, r1⟩ := i₁
  obtain ⟨d0, v0⟩ := s₀
  simp only [ShoumeiSec.Bridge.Queue1_8Impl.step] at *
  bv_decide

/-- Enqueue effect: pushing into an empty queue buffers the operand. -/
theorem push_effect
    (s₀ : ShoumeiSec.Bridge.Queue1_8Impl.State)
    (i₀ i₁ : ShoumeiSec.Bridge.Queue1_8Impl.Inputs)
    (h_rst0 : i₀.reset = 0#1) (h_rst1 : i₁.reset = 0#1)
    (h_empty : (ShoumeiSec.Bridge.Queue1_8Impl.step i₀ s₀).1.valid = 0#1)
    (h_push : i₀.enq_valid = 1#1) :
    let s₁ := (ShoumeiSec.Bridge.Queue1_8Impl.step i₀ s₀).2
    let o₁ := (ShoumeiSec.Bridge.Queue1_8Impl.step i₁ s₁).1
    o₁.valid = 1#1 ∧ o₁.data_reg = i₀.enq_data := by
  obtain ⟨ed0, ev0, dr0, c0, r0⟩ := i₀
  obtain ⟨ed1, ev1, dr1, c1, r1⟩ := i₁
  obtain ⟨d0, v0⟩ := s₀
  simp only [ShoumeiSec.Bridge.Queue1_8Impl.step] at *
  bv_decide

end ShoumeiSec.BridgeQueue1Properties
