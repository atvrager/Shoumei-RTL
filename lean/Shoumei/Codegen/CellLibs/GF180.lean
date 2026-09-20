/-
Codegen/CellLibs/GF180.lean - GF180MCU 9-track 5V standard cells

Cell names, pins and areas read from the GF180MCU Liberty typical (TT) table
under third_party/orfs/flow/platforms/gf180/lib.  GF180 has no non-inverting
composite AND-OR cell, so `.ao21`/`.ao22` are absent: the mapper falls back to
`aoi21`+`inv` (resp. `aoi22`+`inv`).  It does have a real `mux2`.
-/

import Shoumei.Codegen.CellLibrary

namespace Shoumei.Codegen

open Shoumei
open Shoumei.Components

/-- GF180MCU 9T 5V combinational cells (TT, 25C). -/
def gf180Cells : List StandardCell :=
[
    { function := .inv, svName := "gf180mcu_fd_sc_mcu9t5v0__inv_1", outputs := ["ZN"], inputs := ["I"], drive := 1, areaUm2 := 11.2896 },
    { function := .inv, svName := "gf180mcu_fd_sc_mcu9t5v0__inv_2", outputs := ["ZN"], inputs := ["I"], drive := 2, areaUm2 := 16.9344 },
    { function := .inv, svName := "gf180mcu_fd_sc_mcu9t5v0__inv_4", outputs := ["ZN"], inputs := ["I"], drive := 4, areaUm2 := 28.224 },
    { function := .buf, svName := "gf180mcu_fd_sc_mcu9t5v0__buf_1", outputs := ["Z"], inputs := ["I"], drive := 1, areaUm2 := 16.9344 },
    { function := .buf, svName := "gf180mcu_fd_sc_mcu9t5v0__buf_2", outputs := ["Z"], inputs := ["I"], drive := 2, areaUm2 := 22.5792 },
    { function := .buf, svName := "gf180mcu_fd_sc_mcu9t5v0__buf_4", outputs := ["Z"], inputs := ["I"], drive := 4, areaUm2 := 39.5136 },
    { function := .buf, svName := "gf180mcu_fd_sc_mcu9t5v0__buf_8", outputs := ["Z"], inputs := ["I"], drive := 8, areaUm2 := 73.3824 },
    { function := .and2, svName := "gf180mcu_fd_sc_mcu9t5v0__and2_1", outputs := ["Z"], inputs := ["A1", "A2"], drive := 1, areaUm2 := 22.5792 },
    { function := .and2, svName := "gf180mcu_fd_sc_mcu9t5v0__and2_2", outputs := ["Z"], inputs := ["A1", "A2"], drive := 2, areaUm2 := 25.4016 },
    { function := .and2, svName := "gf180mcu_fd_sc_mcu9t5v0__and2_4", outputs := ["Z"], inputs := ["A1", "A2"], drive := 4, areaUm2 := 47.9808 },
    { function := .or2, svName := "gf180mcu_fd_sc_mcu9t5v0__or2_1", outputs := ["Z"], inputs := ["A1", "A2"], drive := 1, areaUm2 := 22.5792 },
    { function := .or2, svName := "gf180mcu_fd_sc_mcu9t5v0__or2_2", outputs := ["Z"], inputs := ["A1", "A2"], drive := 2, areaUm2 := 28.224 },
    { function := .or2, svName := "gf180mcu_fd_sc_mcu9t5v0__or2_4", outputs := ["Z"], inputs := ["A1", "A2"], drive := 4, areaUm2 := 50.8032 },
    { function := .xor2, svName := "gf180mcu_fd_sc_mcu9t5v0__xor2_1", outputs := ["Z"], inputs := ["A1", "A2"], drive := 1, areaUm2 := 33.8688 },
    { function := .xor2, svName := "gf180mcu_fd_sc_mcu9t5v0__xor2_2", outputs := ["Z"], inputs := ["A1", "A2"], drive := 2, areaUm2 := 47.9808 },
    { function := .xor2, svName := "gf180mcu_fd_sc_mcu9t5v0__xor2_4", outputs := ["Z"], inputs := ["A1", "A2"], drive := 4, areaUm2 := 59.2704 },
    { function := .nand2, svName := "gf180mcu_fd_sc_mcu9t5v0__nand2_1", outputs := ["ZN"], inputs := ["A1", "A2"], drive := 1, areaUm2 := 14.112 },
    { function := .nand2, svName := "gf180mcu_fd_sc_mcu9t5v0__nand2_2", outputs := ["ZN"], inputs := ["A1", "A2"], drive := 2, areaUm2 := 25.4016 },
    { function := .nand2, svName := "gf180mcu_fd_sc_mcu9t5v0__nand2_4", outputs := ["ZN"], inputs := ["A1", "A2"], drive := 4, areaUm2 := 45.1584 },
    { function := .nor2, svName := "gf180mcu_fd_sc_mcu9t5v0__nor2_1", outputs := ["ZN"], inputs := ["A1", "A2"], drive := 1, areaUm2 := 16.9344 },
    { function := .nor2, svName := "gf180mcu_fd_sc_mcu9t5v0__nor2_2", outputs := ["ZN"], inputs := ["A1", "A2"], drive := 2, areaUm2 := 28.224 },
    { function := .nor2, svName := "gf180mcu_fd_sc_mcu9t5v0__nor2_4", outputs := ["ZN"], inputs := ["A1", "A2"], drive := 4, areaUm2 := 50.8032 },
    { function := .aoi21, svName := "gf180mcu_fd_sc_mcu9t5v0__aoi21_1", outputs := ["ZN"], inputs := ["A1", "A2", "B"], drive := 1, areaUm2 := 22.5792 },
    { function := .aoi21, svName := "gf180mcu_fd_sc_mcu9t5v0__aoi21_2", outputs := ["ZN"], inputs := ["A1", "A2", "B"], drive := 2, areaUm2 := 36.6912 },
    { function := .aoi21, svName := "gf180mcu_fd_sc_mcu9t5v0__aoi21_4", outputs := ["ZN"], inputs := ["A1", "A2", "B"], drive := 4, areaUm2 := 67.7376 },
    { function := .aoi22, svName := "gf180mcu_fd_sc_mcu9t5v0__aoi22_1", outputs := ["ZN"], inputs := ["A1", "A2", "B1", "B2"], drive := 1, areaUm2 := 25.4016 },
    { function := .aoi22, svName := "gf180mcu_fd_sc_mcu9t5v0__aoi22_2", outputs := ["ZN"], inputs := ["A1", "A2", "B1", "B2"], drive := 2, areaUm2 := 45.1584 },
    { function := .aoi22, svName := "gf180mcu_fd_sc_mcu9t5v0__aoi22_4", outputs := ["ZN"], inputs := ["A1", "A2", "B1", "B2"], drive := 4, areaUm2 := 87.4944 },
    { function := .oai21, svName := "gf180mcu_fd_sc_mcu9t5v0__oai21_1", outputs := ["ZN"], inputs := ["A1", "A2", "B"], drive := 1, areaUm2 := 22.5792 },
    { function := .oai21, svName := "gf180mcu_fd_sc_mcu9t5v0__oai21_2", outputs := ["ZN"], inputs := ["A1", "A2", "B"], drive := 2, areaUm2 := 39.5136 },
    { function := .oai21, svName := "gf180mcu_fd_sc_mcu9t5v0__oai21_4", outputs := ["ZN"], inputs := ["A1", "A2", "B"], drive := 4, areaUm2 := 73.3824 },
    { function := .mux2, svName := "gf180mcu_fd_sc_mcu9t5v0__mux2_1", outputs := ["Z"], inputs := ["I0", "I1", "S"], drive := 1, areaUm2 := 36.6912 },
    { function := .mux2, svName := "gf180mcu_fd_sc_mcu9t5v0__mux2_2", outputs := ["Z"], inputs := ["I0", "I1", "S"], drive := 2, areaUm2 := 42.336 },
    { function := .mux2, svName := "gf180mcu_fd_sc_mcu9t5v0__mux2_4", outputs := ["Z"], inputs := ["I0", "I1", "S"], drive := 4, areaUm2 := 53.6256 },
    { function := .fa, svName := "gf180mcu_fd_sc_mcu9t5v0__addf_1", outputs := ["S", "CO"], inputs := ["A", "B", "CI"], drive := 1, areaUm2 := 84.672 },
    { function := .fa, svName := "gf180mcu_fd_sc_mcu9t5v0__addf_2", outputs := ["S", "CO"], inputs := ["A", "B", "CI"], drive := 2, areaUm2 := 95.9616 },
    { function := .fa, svName := "gf180mcu_fd_sc_mcu9t5v0__addf_4", outputs := ["S", "CO"], inputs := ["A", "B", "CI"], drive := 4, areaUm2 := 118.5408 },
    { function := .ha, svName := "gf180mcu_fd_sc_mcu9t5v0__addh_1", outputs := ["S", "CO"], inputs := ["A", "B"], drive := 1, areaUm2 := 47.9808 },
    { function := .ha, svName := "gf180mcu_fd_sc_mcu9t5v0__addh_2", outputs := ["S", "CO"], inputs := ["A", "B"], drive := 2, areaUm2 := 59.2704 },
    { function := .ha, svName := "gf180mcu_fd_sc_mcu9t5v0__addh_4", outputs := ["S", "CO"], inputs := ["A", "B"], drive := 4, areaUm2 := 107.2512 },
]

/-- Net-fanout ceilings to drive strength, descending. -/
def gf180Fanout : List (Nat × Nat) :=
  [(1, 1), (2, 2), (4, 4), (6, 6), (8, 8), (12, 12), (16, 16), (24, 24), (64, 64)]

/-- The GF180MCU 9T 5V library. -/
def gf180Library : CellLibrary :=
  { pdk := .gf180mcu, cells := gf180Cells, maxFanout := gf180Fanout }

end Shoumei.Codegen
