import Shoumei.RISCV.ISA
import Shoumei.RISCV.Config
import Shoumei.RISCV.Renaming.RenameStage
import Shoumei.RISCV.Renaming.PhysRegFile
import Shoumei.DSL
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.Arbiter

namespace Shoumei.RISCV.Execution

open Shoumei
open Shoumei.Circuits.Combinational

/-- Helper: Create indexed wires -/
private def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

-- Disable unused variables warning for work-in-progress circuit declaration
set_option linter.unusedVariables false

/-- Note: This is a placeholder for the dual-issue reservation station.
    We are just stubbing it out for now.
-/
def mkReservationStation4_W2 (enableStoreLoadOrdering : Bool := false) : Circuit :=
  let clock := Wire.mk "clock"
  let reset := Wire.mk "reset"
  let zero := Wire.mk "zero"
  let one := Wire.mk "one"

  let opcodeWidth := 6
  let tagWidth := 6
  let dataWidth := 32
  let entryWidth := 1 + opcodeWidth + tagWidth + 1 + tagWidth + dataWidth + 1 + tagWidth + dataWidth

  -- Issue interface (W=2)
  let issue_en_0 := Wire.mk "issue_en_0"
  let issue_en_1 := Wire.mk "issue_en_1"
  let issue_is_store_0 := Wire.mk "issue_is_store_0"
  let issue_is_store_1 := Wire.mk "issue_is_store_1"
  let issue_opcode_0 := makeIndexedWires "issue_opcode_0" opcodeWidth
  let issue_dest_tag_0 := makeIndexedWires "issue_dest_tag_0" tagWidth
  let issue_src1_ready_0 := Wire.mk "issue_src1_ready_0"
  let issue_src1_tag_0 := makeIndexedWires "issue_src1_tag_0" tagWidth
  let issue_src1_data_0 := makeIndexedWires "issue_src1_data_0" dataWidth
  let issue_src2_ready_0 := Wire.mk "issue_src2_ready_0"
  let issue_src2_tag_0 := makeIndexedWires "issue_src2_tag_0" tagWidth
  let issue_src2_data_0 := makeIndexedWires "issue_src2_data_0" dataWidth
  
  let issue_opcode_1 := makeIndexedWires "issue_opcode_1" opcodeWidth
  let issue_dest_tag_1 := makeIndexedWires "issue_dest_tag_1" tagWidth
  let issue_src1_ready_1 := Wire.mk "issue_src1_ready_1"
  let issue_src1_tag_1 := makeIndexedWires "issue_src1_tag_1" tagWidth
  let issue_src1_data_1 := makeIndexedWires "issue_src1_data_1" dataWidth
  let issue_src2_ready_1 := Wire.mk "issue_src2_ready_1"
  let issue_src2_tag_1 := makeIndexedWires "issue_src2_tag_1" tagWidth
  let issue_src2_data_1 := makeIndexedWires "issue_src2_data_1" dataWidth

  let alloc_avail_0 := Wire.mk "alloc_avail_0"
  let alloc_avail_1 := Wire.mk "alloc_avail_1"

  -- CDB interface (W=2)
  let cdb_valid_0 := Wire.mk "cdb_valid_0"
  let cdb_tag_0 := makeIndexedWires "cdb_tag_0" tagWidth
  let cdb_data_0 := makeIndexedWires "cdb_data_0" dataWidth
  let cdb_valid_1 := Wire.mk "cdb_valid_1"
  let cdb_tag_1 := makeIndexedWires "cdb_tag_1" tagWidth
  let cdb_data_1 := makeIndexedWires "cdb_data_1" dataWidth

  -- Dispatch interface (W=2)
  -- Currently for ReservationStation4 we might only dispatch W=1 per RS group,
  -- but we typically want it to be dual-dispatch or have multiple RS groups.
  -- For now we implement single dispatch out.
  let dispatch_en := Wire.mk "dispatch_en"
  let dispatch_valid := Wire.mk "dispatch_valid"
  let dispatch_opcode := makeIndexedWires "dispatch_opcode" opcodeWidth
  let dispatch_src1_data := makeIndexedWires "dispatch_src1_data" dataWidth
  let dispatch_src2_data := makeIndexedWires "dispatch_src2_data" dataWidth
  let dispatch_dest_tag := makeIndexedWires "dispatch_dest_tag" tagWidth

  { name := "ReservationStation4_W2"
    inputs := [clock, reset, zero, one, issue_en_0, issue_en_1] ++
              (if enableStoreLoadOrdering then [issue_is_store_0, issue_is_store_1] else []) ++
              issue_opcode_0 ++ issue_dest_tag_0 ++ [issue_src1_ready_0] ++ issue_src1_tag_0 ++ issue_src1_data_0 ++
              [issue_src2_ready_0] ++ issue_src2_tag_0 ++ issue_src2_data_0 ++
              issue_opcode_1 ++ issue_dest_tag_1 ++ [issue_src1_ready_1] ++ issue_src1_tag_1 ++ issue_src1_data_1 ++
              [issue_src2_ready_1] ++ issue_src2_tag_1 ++ issue_src2_data_1 ++
              [cdb_valid_0] ++ cdb_tag_0 ++ cdb_data_0 ++
              [cdb_valid_1] ++ cdb_tag_1 ++ cdb_data_1 ++
              [dispatch_en]
    outputs := [alloc_avail_0, alloc_avail_1, dispatch_valid] ++
               dispatch_opcode ++ dispatch_src1_data ++
               dispatch_src2_data ++ dispatch_dest_tag
    gates := [Gate.mkBUF zero alloc_avail_0, Gate.mkBUF zero alloc_avail_1, Gate.mkBUF zero dispatch_valid] ++
             (dispatch_opcode.map (fun w => Gate.mkBUF zero w)) ++
             (dispatch_src1_data.map (fun w => Gate.mkBUF zero w)) ++
             (dispatch_src2_data.map (fun w => Gate.mkBUF zero w)) ++
             (dispatch_dest_tag.map (fun w => Gate.mkBUF zero w))
    instances := [] }

end Shoumei.RISCV.Execution
