/-
GenerateAdderMatrix.lean - emit the adder calibration matrix

Writes every selectable adder (structure x width x carry mode) plus a thin
clocked `_synth` wrapper into `output/adder-matrix/`, and a `manifest.txt` of
`<module>,<width>,<cin>` lines.  `scripts/calibrate-adders.py` synthesizes each
wrapper per PDK to derive real area/delay, which keeps the analytic constants in
`Shoumei.Components.Cost` honest.

This is tooling only: the selector never reads the matrix or its results.
-/

import Shoumei.Codegen.SystemVerilog
import Shoumei.Components.Select

open Shoumei
open Shoumei.Components
open Shoumei.Circuits.Combinational

/-- Widths and carry modes the matrix covers. -/
def matrixWidths : List Nat := [8, 16, 32, 64, 106]
def matrixCins : List CinMode := [.none, .input, .one]

/-- Every legal (structure, width, carry mode) combination. -/
def matrixSpecs : List AdderSpec :=
  matrixWidths.flatMap fun w =>
    matrixCins.map fun c => { AdderSpec.minArea w c with aim := .minDelay }

/-- Manifest line: module, width, carry mode, and the analytic estimates for
    both PDKs, so `scripts/calibrate-adders.py --refit` can compare measured
    against analytic cost. -/
def manifestLine (spec : AdderSpec) (c : Circuit) : String :=
  let cinTag := match spec.cin with
    | .none => "none" | .input => "input" | .one => "one"
  let est (pdk : PDK) := s!"{estArea pdk c},{estDelay pdk c}"
  s!"{c.name},{spec.width},{cinTag},{est .asap7},{est .gf180mcu}"

/-- Emit the synthesis wrapper: registered inputs, adder, registered output. -/
def synthWrapper (spec : AdderSpec) : String :=
  let w := spec.width
  let name := adderModule spec
  let hasCin := spec.cin == .input
  let cinPort := if hasCin then ",\n  input logic cin" else ""
  let cinDecl := if hasCin then "\n  logic cin_q;" else ""
  let cinReg := if hasCin then "\n    cin_q <= cin;" else ""
  let cinConn := if hasCin then "\n    .cin(cin_q)," else ""
  String.intercalate "\n" [
    s!"// Calibration wrapper for {name} (registered I/O).",
    s!"module {name}_synth (",
    s!"  input logic clock,",
    s!"  input logic [{w - 1}:0] a,",
    s!"  input logic [{w - 1}:0] b{cinPort},",
    s!"  output logic [{w - 1}:0] sum",
    ");",
    s!"  logic [{w - 1}:0] a_q;",
    s!"  logic [{w - 1}:0] b_q;",
    s!"  logic [{w - 1}:0] sum_c;{cinDecl}",
    "",
    "  always_ff @(posedge clock) begin",
    "    a_q <= a;",
    s!"    b_q <= b;{cinReg}",
    "  end",
    "",
    s!"  {name} u_dut (",
    "    .a(a_q),",
    "    .b(b_q),",
    cinConn,
    "    .sum(sum_c)",
    "  );",
    "",
    "  always_ff @(posedge clock) sum <= sum_c;",
    "endmodule",
    ""
  ]

def main : IO Unit := do
  let dir := "output/adder-matrix"
  IO.FS.createDirAll dir
  let mut manifest : List String := []
  for spec in matrixSpecs do
    for impl in AdderImpl.all do
      if !legal impl spec then continue
      let c := adderCircuit impl spec
      IO.FS.writeFile s!"{dir}/{c.name}.sv" (Shoumei.Codegen.SystemVerilog.toSystemVerilog c)
      IO.FS.writeFile s!"{dir}/{c.name}_synth.sv" (synthWrapper { spec with pinned := some impl })
      manifest := manifest ++ [manifestLine spec c]
  IO.FS.writeFile s!"{dir}/manifest.txt" (String.intercalate "\n" manifest ++ "\n")
  IO.println s!"✓ Wrote {manifest.length} adder wrappers to {dir}/"
