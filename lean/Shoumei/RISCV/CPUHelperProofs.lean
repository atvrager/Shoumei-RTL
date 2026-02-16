/-
CPUHelperProofs.lean - Proofs for CPU helper behavioral specifications

Behavioral proofs verifying the CPUHelperSpecs pure functions against
expected behavior for concrete test vectors.
-/

import Shoumei.RISCV.CPUHelperSpecs
import Shoumei.RISCV.Config
import Shoumei.RISCV.ISA

namespace Shoumei.RISCV.CPUHelperProofs

open Shoumei.RISCV
open Shoumei.RISCV.CPUHelperSpecs

/-! ## 1. Serialize Detect Spec Proofs -/

/-- FENCE.I detected when Zifencei enabled and decode valid -/
theorem serialize_fencei_detected :
    let config : CPUConfig := { enableZifencei := true, enableZicsr := false }
    (serializeDetectSpec config .FENCE_I true false).1 = true := by native_decide

/-- CSR detected when Zicsr enabled and decode valid -/
theorem serialize_csr_detected_csrrw :
    let config : CPUConfig := { enableZicsr := true }
    (serializeDetectSpec config .CSRRW true false).2 = true := by native_decide

/-- Nothing detected when redirect active -/
theorem serialize_nothing_on_redirect :
    let config : CPUConfig := { enableZifencei := true, enableZicsr := true }
    serializeDetectSpec config .FENCE_I true true = (false, false) := by native_decide

/-- Nothing detected when decode invalid -/
theorem serialize_nothing_on_invalid :
    let config : CPUConfig := { enableZifencei := true, enableZicsr := true }
    serializeDetectSpec config .FENCE_I false false = (false, false) := by native_decide

/-- ADD doesn't trigger serialize -/
theorem serialize_add_not_detected :
    let config : CPUConfig := { enableZifencei := true, enableZicsr := true }
    serializeDetectSpec config .ADD true false = (false, false) := by native_decide

/-- All 6 CSR opcodes detected -/
theorem serialize_all_csr_ops :
    let config : CPUConfig := { enableZicsr := true }
    let test (op : OpType) := (serializeDetectSpec config op true false).2
    test .CSRRW && test .CSRRS && test .CSRRC &&
    test .CSRRWI && test .CSRRSI && test .CSRRCI = true := by native_decide

/-! ## 2. CSR Address Decode Spec Proofs -/

/-- mscratch address decodes correctly -/
theorem csr_addr_mscratch :
    (csrAddrDecodeSpec 0x340).isMscratch = true := by native_decide

/-- mcycle M-mode address decodes correctly -/
theorem csr_addr_mcycle_m :
    (csrAddrDecodeSpec 0xB00).isMcycle = true := by native_decide

/-- mcycle U-mode alias also matches -/
theorem csr_addr_mcycle_u :
    (csrAddrDecodeSpec 0xC00).isMcycle = true := by native_decide

/-- misa address decodes correctly -/
theorem csr_addr_misa :
    (csrAddrDecodeSpec 0x301).isMisa = true := by native_decide

/-- mstatus address decodes correctly -/
theorem csr_addr_mstatus :
    (csrAddrDecodeSpec 0x300).isMstatus = true := by native_decide

/-- mepc address decodes correctly -/
theorem csr_addr_mepc :
    (csrAddrDecodeSpec 0x341).isMepc = true := by native_decide

/-- Unknown address matches nothing -/
theorem csr_addr_unknown :
    let m := csrAddrDecodeSpec 0x999
    m.isMscratch = false ∧ m.isMcycle = false ∧ m.isMisa = false ∧
    m.isMstatus = false ∧ m.isMepc = false := by native_decide

/-- fflags address decodes correctly -/
theorem csr_addr_fflags :
    (csrAddrDecodeSpec 0x001).isFflags = true := by native_decide

/-- frm address decodes correctly -/
theorem csr_addr_frm :
    (csrAddrDecodeSpec 0x002).isFrm = true := by native_decide

/-- fcsr address decodes correctly -/
theorem csr_addr_fcsr :
    (csrAddrDecodeSpec 0x003).isFcsr = true := by native_decide

/-! ## 3. CSR Op Decode Spec Proofs -/

/-- CSRRW decodes as RW -/
theorem csr_op_csrrw :
    let config : CPUConfig := { enableZicsr := true }
    let op := csrOpDecodeSpec config .CSRRW
    op.isRW = true ∧ op.isRS = false ∧ op.isRC = false ∧ op.isImm = false := by native_decide

/-- CSRRS decodes as RS -/
theorem csr_op_csrrs :
    let config : CPUConfig := { enableZicsr := true }
    let op := csrOpDecodeSpec config .CSRRS
    op.isRW = false ∧ op.isRS = true ∧ op.isRC = false ∧ op.isImm = false := by native_decide

/-- CSRRC decodes as RC -/
theorem csr_op_csrrc :
    let config : CPUConfig := { enableZicsr := true }
    let op := csrOpDecodeSpec config .CSRRC
    op.isRW = false ∧ op.isRS = false ∧ op.isRC = true ∧ op.isImm = false := by native_decide

/-- CSRRWI decodes as RW + IMM -/
theorem csr_op_csrrwi :
    let config : CPUConfig := { enableZicsr := true }
    let op := csrOpDecodeSpec config .CSRRWI
    op.isRW = true ∧ op.isImm = true := by native_decide

/-- Without Zicsr, all flags are false -/
theorem csr_op_disabled :
    let config : CPUConfig := { enableZicsr := false }
    let op := csrOpDecodeSpec config .CSRRW
    op.isRW = false ∧ op.isRS = false ∧ op.isRC = false ∧ op.isImm = false := by native_decide

/-! ## 4. CSR Write Logic Spec Proofs -/

/-- CSRRW: write value is source data -/
theorem csr_write_rw :
    let op : CsrOpDecoded := { isRW := true, isRS := false, isRC := false, isImm := false }
    csrWriteValueSpec 0xFF00 0x1234 op = 0x1234 := by native_decide

/-- CSRRS: write value is OR of read and source -/
theorem csr_write_rs :
    let op : CsrOpDecoded := { isRW := false, isRS := true, isRC := false, isImm := false }
    csrWriteValueSpec 0xFF00 0x00FF op = 0xFFFF := by native_decide

/-- CSRRC: write value clears source bits -/
theorem csr_write_rc :
    let op : CsrOpDecoded := { isRW := false, isRS := false, isRC := true, isImm := false }
    csrWriteValueSpec 0xFFFF 0x00FF op = 0xFF00 := by native_decide

/-- RW always writes -/
theorem csr_actually_writes_rw :
    let op : CsrOpDecoded := { isRW := true, isRS := false, isRC := false, isImm := false }
    csrActuallyWrites op false = true := by native_decide

/-- RS with zimm=0 doesn't write -/
theorem csr_rs_zero_no_write :
    let op : CsrOpDecoded := { isRW := false, isRS := true, isRC := false, isImm := false }
    csrActuallyWrites op false = false := by native_decide

/-- RS with nonzero zimm writes -/
theorem csr_rs_nonzero_writes :
    let op : CsrOpDecoded := { isRW := false, isRS := true, isRC := false, isImm := false }
    csrActuallyWrites op true = true := by native_decide

/-- Write enable requires drain_complete AND actually_writes AND csr_match -/
theorem csr_we_all_required :
    csrWriteEnable true true true = true ∧
    csrWriteEnable false true true = false ∧
    csrWriteEnable true false true = false ∧
    csrWriteEnable true true false = false := by native_decide

/-! ## 5. CSR Next Value Spec Proofs -/

/-- csrNextValue holds when write disabled -/
theorem csr_next_hold :
    csrNextValueSpec 42 99 false = 42 := by native_decide

/-- csrNextValue updates when write enabled -/
theorem csr_next_update :
    csrNextValueSpec 42 99 true = 99 := by native_decide

/-- mcycle auto-increments when no write -/
theorem mcycle_auto_increment :
    mcycleNextSpec 100 0 false = 101 := by native_decide

/-- mcycle write overrides auto-increment -/
theorem mcycle_write_override :
    mcycleNextSpec 100 500 true = 500 := by native_decide

/-- minstret increments on commit -/
theorem minstret_commit_increment :
    minstretNextSpec 50 0 false true = 51 := by native_decide

/-- minstret holds when no commit and no write -/
theorem minstret_no_commit_hold :
    minstretNextSpec 50 0 false false = 50 := by native_decide

/-- minstret write overrides -/
theorem minstret_write_override :
    minstretNextSpec 50 200 true false = 200 := by native_decide

/-! ## 6. WARL Mask Proofs -/

/-- mie WARL: only bits 3, 7, 11 pass through -/
theorem mie_warl_mask_correct :
    mieWarlMask 0xFFFFFFFF = ((1 : UInt32) <<< 3 ||| (1 : UInt32) <<< 7 ||| (1 : UInt32) <<< 11) := by native_decide

/-- mtvec WARL: bit 1 is cleared -/
theorem mtvec_warl_clears_bit1 :
    mtvecWarlMask 0xFF = 0xFD := by native_decide

/-- mepc WARL: bits 1:0 are cleared -/
theorem mepc_warl_clears_low_bits :
    mepcWarlMask 0xFF = 0xFC := by native_decide

/-! ## 7. Load Forwarding Spec Proofs -/

/-- Word load with word-size SB entry: forward valid -/
theorem load_fwd_word_match :
    let r := loadForwardingSpec 2 2 true false false true true false false
    r.fwdValid = true := by native_decide

/-- Byte load with word-size SB entry: forward valid (store covers load) -/
theorem load_fwd_byte_from_word :
    let r := loadForwardingSpec 0 2 true false false true true false false
    r.fwdValid = true := by native_decide

/-- Word load with byte-size SB entry: cross-size stall -/
theorem load_fwd_word_from_byte_stall :
    let r := loadForwardingSpec 2 0 true false false true true false false
    r.fwdValid = false ∧ r.crossSizeStall = true := by native_decide

/-- No SB hit: no forwarding, no stall -/
theorem load_fwd_no_hit :
    let r := loadForwardingSpec 2 2 false false false true true false false
    r.fwdValid = false ∧ r.crossSizeStall = false := by native_decide

/-- Word-only overlap causes stall during dispatch -/
theorem load_fwd_word_overlap_stall :
    let r := loadForwardingSpec 2 2 false false true true true true true
    r.crossSizeStall = true := by native_decide

/-! ## 8. Source Selection Proofs -/

/-- Register mode: return full register data -/
theorem csr_source_reg :
    csrSelectSource false 0xDEADBEEF 0x1F = 0xDEADBEEF := by native_decide

/-- Immediate mode: return zero-extended 5-bit immediate -/
theorem csr_source_imm :
    csrSelectSource true 0xDEADBEEF 0xFF = 0x1F := by native_decide

end Shoumei.RISCV.CPUHelperProofs
