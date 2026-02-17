/-
CPUHelperSpecs.lean - Behavioral specifications for CPU helper functions

Pure-function specifications that describe the intended behavior of the
gate-level helper functions in CPU.lean:
  mkSerializeDetect, mkMemPipeline, mkLoadForwarding,
  mkCsrAddrDecode, mkCsrReadMux, mkCsrOpDecode,
  mkCsrWriteLogic, mkCsrNextValue
-/

import Shoumei.RISCV.Config
import Shoumei.RISCV.ISA

namespace Shoumei.RISCV.CPUHelperSpecs

open Shoumei.RISCV

/-! ## CSR Address Constants -/

def CSR_MSCRATCH  : UInt32 := 0x340
def CSR_MCYCLE_M  : UInt32 := 0xB00
def CSR_MCYCLE_U  : UInt32 := 0xC00
def CSR_MCYCLEH_M : UInt32 := 0xB80
def CSR_MCYCLEH_U : UInt32 := 0xC80
def CSR_MINSTRET_M  : UInt32 := 0xB02
def CSR_MINSTRET_U  : UInt32 := 0xC02
def CSR_MINSTRETH_M : UInt32 := 0xB82
def CSR_MINSTRETH_U : UInt32 := 0xC82
def CSR_MISA      : UInt32 := 0x301
def CSR_MHARTID   : UInt32 := 0xF14
def CSR_FFLAGS    : UInt32 := 0x001
def CSR_FRM       : UInt32 := 0x002
def CSR_FCSR      : UInt32 := 0x003
def CSR_MSTATUS   : UInt32 := 0x300
def CSR_MIE       : UInt32 := 0x304
def CSR_MTVEC     : UInt32 := 0x305
def CSR_MEPC      : UInt32 := 0x341
def CSR_MCAUSE    : UInt32 := 0x342
def CSR_MTVAL     : UInt32 := 0x343
def CSR_MIP       : UInt32 := 0x344

/-! ## 1. Serialize Detect Spec -/

/-- Determines which serialization event is detected from the current decode optype.
    Returns (fence_i_detected, csr_detected). -/
def serializeDetectSpec (config : CPUConfig) (opType : OpType) (decodeValid : Bool) (redirectActive : Bool) : Bool × Bool :=
  let validDecode := decodeValid && !redirectActive
  let fenceI := config.enableZifencei && validDecode && opType == .FENCE_I
  let csr := config.enableZicsr && validDecode &&
    (opType == .CSRRW || opType == .CSRRS || opType == .CSRRC ||
     opType == .CSRRWI || opType == .CSRRSI || opType == .CSRRCI)
  (fenceI, csr)

/-! ## 2. Memory Pipeline Spec -/

/-- Memory pipeline register hold/load semantics.
    When enabled, loads new values; otherwise holds previous values. -/
structure MemPipeState where
  addr : UInt32
  tag : UInt32   -- 6-bit tag stored as UInt32
  isLoad : Bool
  memSize : UInt32  -- 2-bit size
  signExtend : Bool
  isFlw : Bool
  valid : Bool
deriving Repr, BEq, DecidableEq

/-- Compute next memory pipeline state.
    pipeEn: new dispatch is valid and not flushing
    loadCompleting: the load in the pipeline is completing (fwd or no-fwd)
    flushing: pipeline flush active -/
def memPipelineSpec (prev : MemPipeState) (pipeEn : Bool)
    (newAddr : UInt32) (newTag : UInt32) (newIsLoad : Bool) (newSize : UInt32) (newSignExt : Bool) (newIsFlw : Bool)
    (loadCompleting : Bool) (flushing : Bool) : MemPipeState :=
  let nextValid := (pipeEn || (prev.valid && prev.isLoad && !loadCompleting)) && !flushing
  if pipeEn then
    { addr := newAddr, tag := newTag, isLoad := newIsLoad, memSize := newSize,
      signExtend := newSignExt, isFlw := newIsFlw, valid := nextValid }
  else
    { prev with valid := nextValid }

/-! ## 3. Load Forwarding Spec -/

/-- Load forwarding result from store buffer. -/
structure LoadFwdResult where
  fwdValid : Bool          -- SB forwarding is valid (size OK, no partial overlap)
  crossSizeStall : Bool    -- Size mismatch stall (includes word overlap)
  crossSizeUncommitted : Bool  -- Size mismatch on uncommitted entry
deriving Repr, BEq, DecidableEq

/-- Compute load forwarding result.
    loadSize: 2-bit size (00=byte, 01=half, 10=word)
    fwdSize: 2-bit size of matching SB entry
    sbHit: SB has matching address
    sbWordOnlyHit: SB has entry at same word but different byte offset
    memValid: pipeline stage valid
    isLoad: instruction is a load -/
def loadForwardingSpec (loadSize fwdSize : UInt32) (sbHit sbCommittedHit sbWordOnlyHit : Bool)
    (memValid isLoadR : Bool) (rsMemDispatchValid isLoad : Bool) : LoadFwdResult :=
  -- Size check: fwd OK when store covers the full load
  -- fwd_size_ok = fwdSize[1] OR (NOT(loadSize[1]) AND (fwdSize[0] OR NOT(loadSize[0])))
  let fwdSizeOk := (fwdSize &&& 2 != 0) || ((loadSize &&& 2 == 0) && ((fwdSize &&& 1 != 0) || (loadSize &&& 1 == 0)))
  let loadFwdPre := sbHit && memValid && isLoadR && fwdSizeOk
  let fwdValid := loadFwdPre && !sbWordOnlyHit
  let crossSizeAny := sbHit && memValid && isLoadR && !fwdSizeOk
  let wordOverlapStall := sbWordOnlyHit && rsMemDispatchValid && isLoad
  let crossSizeStall := crossSizeAny || wordOverlapStall
  let crossSizeUncommitted := crossSizeAny && !sbCommittedHit
  { fwdValid, crossSizeStall, crossSizeUncommitted }

/-! ## 4. CSR Address Decode Spec -/

/-- CSR address decode result: which CSR matches the 12-bit address. -/
structure CsrAddrMatch where
  isMscratch : Bool
  isMcycle : Bool      -- M-mode OR U-mode alias
  isMcycleh : Bool
  isMinstret : Bool
  isMinstreth : Bool
  isMisa : Bool
  isFflags : Bool
  isFrm : Bool
  isFcsr : Bool
  isMstatus : Bool
  isMie : Bool
  isMtvec : Bool
  isMepc : Bool
  isMcause : Bool
  isMtval : Bool
  isMip : Bool
deriving Repr, BEq, DecidableEq

/-- Decode a 12-bit CSR address to match flags. -/
def csrAddrDecodeSpec (addr : UInt32) : CsrAddrMatch :=
  let masked := addr &&& 0xFFF
  { isMscratch := masked == CSR_MSCRATCH
    isMcycle := masked == CSR_MCYCLE_M || masked == CSR_MCYCLE_U
    isMcycleh := masked == CSR_MCYCLEH_M || masked == CSR_MCYCLEH_U
    isMinstret := masked == CSR_MINSTRET_M || masked == CSR_MINSTRET_U
    isMinstreth := masked == CSR_MINSTRETH_M || masked == CSR_MINSTRETH_U
    isMisa := masked == CSR_MISA
    isFflags := masked == CSR_FFLAGS
    isFrm := masked == CSR_FRM
    isFcsr := masked == CSR_FCSR
    isMstatus := masked == CSR_MSTATUS
    isMie := masked == CSR_MIE
    isMtvec := masked == CSR_MTVEC
    isMepc := masked == CSR_MEPC
    isMcause := masked == CSR_MCAUSE
    isMtval := masked == CSR_MTVAL
    isMip := masked == CSR_MIP }

/-! ## 5. CSR Read MUX Spec -/

/-- CSR register file state (all CSR values). -/
structure CsrRegState where
  mscratch : UInt32
  mcycle : UInt32
  mcycleh : UInt32
  minstret : UInt32
  minstreth : UInt32
  mstatus : UInt32
  mie : UInt32
  mtvec : UInt32
  mepc : UInt32
  mcause : UInt32
  mtval : UInt32
  fflags : UInt32  -- 5-bit
  frm : UInt32     -- 3-bit
deriving Repr, BEq, DecidableEq

/-- Read the CSR value selected by address decode match flags.
    Returns (readData, mstatus_sd_bit). -/
def csrReadMuxSpec (enableZicsr enableF : Bool) (match_ : CsrAddrMatch) (regs : CsrRegState)
    (misaVal : UInt32) : UInt32 :=
  if !enableZicsr then 0
  else
    let fcsrVal := (regs.frm &&& (0x7 : UInt32)) <<< 5 ||| (regs.fflags &&& (0x1F : UInt32))
    -- Construct mstatus read value with WARL fields
    let mstatusRead : UInt32 :=
      let base := regs.mstatus
      let withMPP := base ||| ((3 : UInt32) <<< 11)
      let withFS := if enableF then
                      let fsInv0 := regs.mstatus &&& ((1 : UInt32) <<< 13) == 0
                      let fsInv1 := regs.mstatus &&& ((1 : UInt32) <<< 14) == 0
                      let sd : UInt32 := if fsInv0 && fsInv1 then 0 else ((1 : UInt32) <<< 31)
                      (withMPP &&& ~~~(((1 : UInt32) <<< 13) ||| ((1 : UInt32) <<< 14))) |||
                        (if fsInv0 then ((1 : UInt32) <<< 13) else 0) |||
                        (if fsInv1 then ((1 : UInt32) <<< 14) else 0) ||| sd
                    else withMPP
      withFS
    -- Priority cascade (last match wins since we use if-else)
    if match_.isMip then (0 : UInt32)
    else if match_.isMtval then regs.mtval
    else if match_.isMcause then regs.mcause
    else if match_.isMepc then regs.mepc
    else if match_.isMtvec then regs.mtvec
    else if match_.isMie then regs.mie
    else if match_.isMstatus then mstatusRead
    else if match_.isFcsr then if enableF then fcsrVal else 0
    else if match_.isFrm then if enableF then regs.frm &&& (0x7 : UInt32) else 0
    else if match_.isFflags then if enableF then regs.fflags &&& (0x1F : UInt32) else 0
    else if match_.isMinstreth then regs.minstreth
    else if match_.isMinstret then regs.minstret
    else if match_.isMcycleh then regs.mcycleh
    else if match_.isMcycle then regs.mcycle
    else if match_.isMscratch then regs.mscratch
    else if match_.isMisa then misaVal
    else 0

/-! ## 6. CSR Op Decode Spec -/

/-- CSR operation decode result. -/
structure CsrOpDecoded where
  isRW : Bool    -- CSRRW or CSRRWI
  isRS : Bool    -- CSRRS or CSRRSI
  isRC : Bool    -- CSRRC or CSRRCI
  isImm : Bool   -- Immediate variant (CSRR*I)
deriving Repr, BEq, DecidableEq

/-- Decode captured CSR optype to operation flags. -/
def csrOpDecodeSpec (config : CPUConfig) (opType : OpType) : CsrOpDecoded :=
  if !config.enableZicsr then
    { isRW := false, isRS := false, isRC := false, isImm := false }
  else
    { isRW := opType == .CSRRW || opType == .CSRRWI
      isRS := opType == .CSRRS || opType == .CSRRSI
      isRC := opType == .CSRRC || opType == .CSRRCI
      isImm := opType == .CSRRWI || opType == .CSRRSI || opType == .CSRRCI }

/-- Select CSR source value: register data or zero-extended immediate. -/
def csrSelectSource (isImm : Bool) (regData : UInt32) (zimm : UInt32) : UInt32 :=
  if isImm then zimm &&& 0x1F else regData

/-! ## 7. CSR Write Logic Spec -/

/-- Compute CSR write value from operation type. -/
def csrWriteValueSpec (readData srcData : UInt32) (op : CsrOpDecoded) : UInt32 :=
  if op.isRC then readData &&& ~~~srcData
  else if op.isRS then readData ||| srcData
  else srcData  -- RW: just write the source

/-- Determine if CSR write actually occurs (RS/RC with rs1=0 doesn't write). -/
def csrActuallyWrites (op : CsrOpDecoded) (zimmNonzero : Bool) : Bool :=
  op.isRW || ((op.isRS || op.isRC) && zimmNonzero)

/-- Generate per-CSR write enable from global write gate and address match. -/
def csrWriteEnable (drainComplete : Bool) (actuallyWrites : Bool) (csrMatch : Bool) : Bool :=
  drainComplete && actuallyWrites && csrMatch

/-! ## 8. CSR Next Value Spec -/

/-- WARL masking for mstatus: only MIE(3), MPIE(7) are writable.
    MPP(12:11) always reads as M. FS(14:13) writable only with F ext (inverted). -/
def mstatusWarlMask (enableF : Bool) (writeVal : UInt32) : UInt32 :=
  let mie_bit := writeVal &&& ((1 : UInt32) <<< 3)
  let mpie_bit := writeVal &&& ((1 : UInt32) <<< 7)
  let mpp : UInt32 := (3 : UInt32) <<< 11
  let fs : UInt32 := if enableF then
              let fs13 : UInt32 := if writeVal &&& ((1 : UInt32) <<< 13) == 0 then ((1 : UInt32) <<< 13) else 0
              let fs14 : UInt32 := if writeVal &&& ((1 : UInt32) <<< 14) == 0 then ((1 : UInt32) <<< 14) else 0
              fs13 ||| fs14
            else 0
  mie_bit ||| mpie_bit ||| mpp ||| fs

/-- WARL masking for mie: only MSIE(3), MTIE(7), MEIE(11) writable. -/
def mieWarlMask (writeVal : UInt32) : UInt32 :=
  (writeVal &&& ((1 : UInt32) <<< 3)) ||| (writeVal &&& ((1 : UInt32) <<< 7)) ||| (writeVal &&& ((1 : UInt32) <<< 11))

/-- WARL masking for mtvec: bit 1 always 0 (only Direct mode supported). -/
def mtvecWarlMask (writeVal : UInt32) : UInt32 :=
  writeVal &&& ~~~((1 : UInt32) <<< 1)

/-- WARL masking for mepc: bits 1:0 always 0 (4-byte aligned). -/
def mepcWarlMask (writeVal : UInt32) : UInt32 :=
  writeVal &&& ~~~((3 : UInt32))

/-- Compute next CSR register value: MUX(hold, masked_write, write_enable). -/
def csrNextValueSpec (currentVal : UInt32) (writeVal : UInt32) (we : Bool) : UInt32 :=
  if we then writeVal else currentVal

/-- Compute next mcycle value: auto-increment by 1, overridden by CSR write. -/
def mcycleNextSpec (currentVal : UInt32) (writeVal : UInt32) (we : Bool) : UInt32 :=
  if we then writeVal else currentVal + 1

/-- Compute next minstret value: auto-increment by 1 on commit, overridden by CSR write. -/
def minstretNextSpec (currentVal : UInt32) (writeVal : UInt32) (we : Bool) (commitValid : Bool) : UInt32 :=
  if we then writeVal
  else if commitValid then currentVal + 1
  else currentVal

end Shoumei.RISCV.CPUHelperSpecs
