/-
Components/Cost.lean - Analytic area/delay model for gate-level circuits

The selector ranks candidate structures by rough area and delay.  These are
*analytic* estimates, refined from real synthesis runs by
`scripts/calibrate-adders.py` (Step 8); they are never read at runtime by the
flow.  Their only job is to pick a plausible structure before synthesis.

Seeds come from the PDK Liberty typical (TT) tables:

  ASAP7 7.5T RVT:    third_party/orfs/flow/platforms/asap7/lib/NLDM/
                       asap7sc7p5t_{SIMPLE,AO,OA,INVBUF}_RVT_TT_nldm_*.lib.gz
                     area unit 1 µm², time unit 1 ps.  Typical gate delay
                     4-15 ps (docs/physical-design.md §"Liberty Timing").
  GF180MCU 9T 5V:    third_party/orfs/flow/platforms/gf180/lib/
                       gf180mcu_fd_sc_mcu9t5v0__tt_025C_5v00.lib.gz
                     area unit 1 µm², time unit 1 ns.  Typical gate delay
                     0.2-1.5 ns.
-/

import Shoumei.DSL
import Shoumei.Components.Spec
import Std.Data.HashMap

namespace Shoumei.Components

open Shoumei

/-- Per-cell area in µm², from the PDK Liberty typical tables. -/
def cellArea (pdk : PDK) (t : GateType) : Float :=
  match pdk with
  | .asap7 =>
      match t with
      | .AND           => 0.08748   -- AND2x2_ASAP7_75t_R
      | .OR            => 0.08748   -- OR2x2_ASAP7_75t_R
      | .XOR           => 0.16038   -- XOR2x2_ASAP7_75t_R
      | .NOT           => 0.04374   -- INVx1_ASAP7_75t_R
      | .BUF           => 0.07290   -- BUFx2_ASAP7_75t_R
      | .MUX           => 0.13122   -- no mux cell; AO22+x2 INV proxy
      | .DFF | .DFF_SET => 0.30
  | .gf180mcu =>
      match t with
      | .AND           => 22.5792   -- and2_1
      | .OR            => 22.5792   -- or2_1
      | .XOR           => 33.8688   -- xor2_1
      | .NOT           => 11.2896   -- inv_1
      | .BUF           => 16.9344   -- buf_1
      | .MUX           => 36.6912   -- mux2_1
      | .DFF | .DFF_SET => 60.0

/-- Per-cell propagation delay in ps, from the PDK Liberty typical tables. -/
def cellDelay (pdk : PDK) (t : GateType) : Float :=
  match pdk with
  | .asap7 =>
      match t with
      | .AND | .OR     => 10.0
      | .XOR           => 14.0
      | .NOT           => 5.0
      | .BUF           => 6.0
      | .MUX           => 12.0
      | .DFF | .DFF_SET => 20.0
  | .gf180mcu =>
      match t with
      | .AND | .OR     => 400.0
      | .XOR           => 600.0
      | .NOT           => 200.0
      | .BUF           => 250.0
      | .MUX           => 500.0
      | .DFF | .DFF_SET => 800.0

/-- Summed cell area of a circuit's gates, µm². -/
def estArea (pdk : PDK) (c : Circuit) : Float :=
  c.gates.foldl (fun acc g => acc + cellArea pdk g.gateType) 0.0

/-- Longest delay-weighted path from a primary input to any gate output, ps.

    Relaxation to a fixpoint: primary inputs cost 0; a gate's arrival is the
    maximum input arrival plus its own cell delay.  Bounded by `gates.length+1`
    sweeps, enough for the deepest path (the repo lint guarantees no
    combinational loops, so the relaxation terminates). -/
def estDelayGates (pdk : PDK) (gates : List Gate) (inputs : List Wire) : Float :=
  let init : Std.HashMap String Float :=
    inputs.foldl (fun m w => m.insert w.name 0.0) {}

  -- One relaxation sweep; also reports whether anything moved, so the loop
  -- stops as soon as the estimate is a fixpoint instead of running the full
  -- `gates.length + 1` bound on every circuit.
  let step (m : Std.HashMap String Float) : Std.HashMap String Float × Bool :=
    gates.foldl (fun (acc, changed) g =>
      let inArr := g.inputs.foldl (fun mx i => max mx (acc.getD i.name 0.0)) 0.0
      let outArr := inArr + cellDelay pdk g.gateType
      if outArr > acc.getD g.output.name 0.0 then (acc.insert g.output.name outArr, true)
      else (acc, changed)
    ) (m, false)

  let rec loop (m : Std.HashMap String Float) (fuel : Nat) : Std.HashMap String Float :=
    match fuel with
    | 0 => m
    | fuel + 1 =>
        let (m', changed) := step m
        if changed then loop m' fuel else m'

  let final := loop init (gates.length + 1)

  (gates.map (·.output)).foldl (fun mx w => max mx (final.getD w.name 0.0)) 0.0

/-- Longest delay-weighted path from any primary input to any primary output, ps. -/
def estDelay (pdk : PDK) (c : Circuit) : Float :=
  estDelayGates pdk c.gates c.inputs

end Shoumei.Components