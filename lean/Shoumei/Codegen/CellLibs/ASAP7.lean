/-
Codegen/CellLibs/ASAP7.lean - ASAP7 7.5T RVT standard cells

Cell names, pins and areas read from the ASAP7 Liberty typical (TT) tables
under third_party/orfs/flow/platforms/asap7/lib/NLDM.

Two gaps are deliberate, and the mapper falls back rather than guess:
  - ASAP7 has no multiplexer cell in any RVT TT library, so `.mux2` is absent
    and the mapper emits a continuous `assign`.
  - ASAP7's `FAx1`/`HAxp5` drive *inverted* sum and carry pins (their Liberty
    functions are the complements), so `.fa`/`.ha` are absent and the mapper
    keeps the `xor2`+`and2` pair there.  GF180's `addf`/`addh` are not
    inverted and are present in that library.
-/

import Shoumei.Codegen.CellLibrary

namespace Shoumei.Codegen

open Shoumei
open Shoumei.Components

/-- ASAP7 7.5T RVT combinational cells (TT corner). -/
def asap7Cells : List StandardCell :=
[
    { function := .inv, svName := "INVx1_ASAP7_75t_R", outputs := ["Y"], inputs := ["A"], drive := 1, areaUm2 := 0.04374 },
    { function := .inv, svName := "INVx2_ASAP7_75t_R", outputs := ["Y"], inputs := ["A"], drive := 2, areaUm2 := 0.05832 },
    { function := .inv, svName := "INVx4_ASAP7_75t_R", outputs := ["Y"], inputs := ["A"], drive := 4, areaUm2 := 0.08748 },
    { function := .inv, svName := "INVx8_ASAP7_75t_R", outputs := ["Y"], inputs := ["A"], drive := 8, areaUm2 := 0.1458 },
    { function := .buf, svName := "BUFx2_ASAP7_75t_R", outputs := ["Y"], inputs := ["A"], drive := 2, areaUm2 := 0.0729 },
    { function := .buf, svName := "BUFx4_ASAP7_75t_R", outputs := ["Y"], inputs := ["A"], drive := 4, areaUm2 := 0.10206 },
    { function := .buf, svName := "BUFx8_ASAP7_75t_R", outputs := ["Y"], inputs := ["A"], drive := 8, areaUm2 := 0.17496 },
    { function := .buf, svName := "BUFx12_ASAP7_75t_R", outputs := ["Y"], inputs := ["A"], drive := 12, areaUm2 := 0.23328 },
    { function := .and2, svName := "AND2x2_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 2, areaUm2 := 0.08748 },
    { function := .and2, svName := "AND2x4_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 4, areaUm2 := 0.1458 },
    { function := .and2, svName := "AND2x6_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 6, areaUm2 := 0.17496 },
    { function := .or2, svName := "OR2x2_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 2, areaUm2 := 0.08748 },
    { function := .or2, svName := "OR2x4_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 4, areaUm2 := 0.11664 },
    { function := .or2, svName := "OR2x6_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 6, areaUm2 := 0.17496 },
    { function := .xor2, svName := "XOR2x1_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 1, areaUm2 := 0.17496 },
    { function := .xor2, svName := "XOR2x2_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 2, areaUm2 := 0.16038 },
    { function := .nand2, svName := "NAND2x1_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 1, areaUm2 := 0.08748 },
    { function := .nand2, svName := "NAND2x2_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 2, areaUm2 := 0.1458 },
    { function := .nor2, svName := "NOR2x1_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 1, areaUm2 := 0.08748 },
    { function := .nor2, svName := "NOR2x2_ASAP7_75t_R", outputs := ["Y"], inputs := ["A", "B"], drive := 2, areaUm2 := 0.1458 },
    { function := .ao21, svName := "AO21x1_ASAP7_75t_R", outputs := ["Y"], inputs := ["A1", "A2", "B"], drive := 1, areaUm2 := 0.08748 },
    { function := .ao21, svName := "AO21x2_ASAP7_75t_R", outputs := ["Y"], inputs := ["A1", "A2", "B"], drive := 2, areaUm2 := 0.10206 },
    { function := .ao22, svName := "AO22x1_ASAP7_75t_R", outputs := ["Y"], inputs := ["A1", "A2", "B1", "B2"], drive := 1, areaUm2 := 0.13122 },
    { function := .ao22, svName := "AO22x2_ASAP7_75t_R", outputs := ["Y"], inputs := ["A1", "A2", "B1", "B2"], drive := 2, areaUm2 := 0.1458 },
    { function := .aoi21, svName := "AOI21x1_ASAP7_75t_R", outputs := ["Y"], inputs := ["A1", "A2", "B"], drive := 1, areaUm2 := 0.11664 },
    { function := .aoi21, svName := "AOI21xp5_ASAP7_75t_R", outputs := ["Y"], inputs := ["A1", "A2", "B"], drive := 1, areaUm2 := 0.0729 },
    { function := .oai21, svName := "OAI21x1_ASAP7_75t_R", outputs := ["Y"], inputs := ["A1", "A2", "B"], drive := 1, areaUm2 := 0.11664 },
    { function := .oai21, svName := "OAI21xp5_ASAP7_75t_R", outputs := ["Y"], inputs := ["A1", "A2", "B"], drive := 1, areaUm2 := 0.0729 },
]

/-- Net-fanout ceilings to drive strength, descending. -/
def asap7Fanout : List (Nat × Nat) :=
  [(1, 1), (2, 2), (4, 4), (6, 6), (8, 8), (12, 12), (16, 16), (24, 24), (64, 64)]

/-- The ASAP7 7.5T RVT library. -/
def asap7Library : CellLibrary :=
  { pdk := .asap7, cells := asap7Cells, maxFanout := asap7Fanout }

end Shoumei.Codegen
