/-
CPU Control Logic - Pipeline Stall and Flush Generation

This module implements centralized control logic for the Tomasulo pipeline:
1. Stall generation - OR of all structural hazards
2. Flush handling - Pipeline recovery from branch misprediction/exception
3. Stage enable signals - Coordination across pipeline stages

The control logic is config-aware and respects M-extension enable/disable.
-/

import Shoumei.RISCV.Config
import Shoumei.RISCV.ISA
import Shoumei.RISCV.Execution.Dispatch

namespace Shoumei.RISCV.Control

open Shoumei.RISCV
open Shoumei.RISCV.Execution

/-
Stall Signal Generation

A stall occurs when any pipeline resource is unavailable. All stall sources
are OR'd together to produce a global stall signal that freezes the fetch stage.

Stall sources (structural hazards):
- FreeList empty: Can't allocate physical register for rename
- ROB full: Can't allocate ROB entry for new instruction
- RS full: Can't issue instruction to appropriate reservation station
- LSU stall: Can't accept new load/store (pending load or store buffer full)

The stall logic is config-aware: when M extension is disabled, attempting
to issue a MulDiv instruction causes a stall (which prevents execution).
-/

/-- Check if an operation needs the Integer RS -/
def needsIntegerRS (op : OpType) (config : CPUConfig) : Bool :=
  classifyToUnit op config == ExecUnit.Integer

/-- Check if an operation needs the Memory RS -/
def needsMemoryRS (op : OpType) (config : CPUConfig) : Bool :=
  classifyToUnit op config == ExecUnit.Memory

/-- Check if an operation needs the Branch RS -/
def needsBranchRS (op : OpType) (config : CPUConfig) : Bool :=
  classifyToUnit op config == ExecUnit.Branch

/-- Check if an operation needs the MulDiv RS -/
def needsMulDivRS (op : OpType) (config : CPUConfig) : Bool :=
  classifyToUnit op config == ExecUnit.MulDiv

/-- Check if an operation is a load -/
def isLoad (op : OpType) : Bool :=
  match op with
  | .LB | .LH | .LW | .LBU | .LHU => true
  | _ => false

/-- Check if an operation is a store -/
def isStore (op : OpType) : Bool :=
  match op with
  | .SB | .SH | .SW => true
  | _ => false

/-- Generate global stall signal from all structural hazard sources.

    Parameters:
    - config: CPU configuration (for M-extension awareness)
    - freeListEmpty: FreeList has no available physical registers
    - robFull: ROB has no free entries
    - rsIntegerFull: Integer RS is full
    - rsMemoryFull: Memory RS is full
    - rsBranchFull: Branch RS is full
    - rsMulDivFull: MulDiv RS is full (only checked if M extension enabled)
    - lsuCanAcceptLoad: LSU can accept a new load
    - lsuCanAcceptStore: LSU can accept a new store
    - instrType: OpType of instruction attempting to issue

    Returns: True if pipeline should stall
-/
def generateStall
    (config : CPUConfig)
    (freeListEmpty : Bool)
    (robFull : Bool)
    (rsIntegerFull : Bool)
    (rsMemoryFull : Bool)
    (rsBranchFull : Bool)
    (rsMulDivFull : Bool)
    (lsuCanAcceptLoad : Bool)
    (lsuCanAcceptStore : Bool)
    (instrType : OpType)
    : Bool :=
  -- All stalls OR'd together
  freeListEmpty || robFull ||
  (needsIntegerRS instrType config && rsIntegerFull) ||
  (needsMemoryRS instrType config && rsMemoryFull) ||
  (needsBranchRS instrType config && rsBranchFull) ||
  (needsMulDivRS instrType config && rsMulDivFull) ||
  (isLoad instrType && !lsuCanAcceptLoad) ||
  (isStore instrType && !lsuCanAcceptStore)

/-
Stage Enable Signals

Controls which pipeline stages can accept new work based on stall and flush conditions.
-/

/-- Stage enable signals for pipeline coordination -/
structure StageEnables where
  /-- Fetch stage can fetch new instruction -/
  fetchEnable : Bool
  /-- Decode stage can accept instruction from fetch -/
  decodeEnable : Bool
  /-- Rename stage can process decoded instruction -/
  renameEnable : Bool
  /-- Issue stage can dispatch to reservation stations -/
  issueEnable : Bool
deriving Repr, BEq

/-- Generate stage enable signals.

    During stall: All stages freeze
    During flush: All stages disabled (flushing)
    Normal: All stages enabled
-/
def generateStageEnables (stall : Bool) (flushing : Bool) : StageEnables :=
  if flushing then
    -- Flush in progress: disable all stages
    { fetchEnable := false
      decodeEnable := false
      renameEnable := false
      issueEnable := false }
  else if stall then
    -- Stall: freeze all stages
    { fetchEnable := false
      decodeEnable := false
      renameEnable := false
      issueEnable := false }
  else
    -- Normal operation: all stages enabled
    { fetchEnable := true
      decodeEnable := true
      renameEnable := true
      issueEnable := true }

/-
Flush Condition Detection

Determines when a pipeline flush is required.
-/

/-- Flush reason enumeration -/
inductive FlushReason where
  | BranchMisprediction : FlushReason
  | Exception : FlushReason
  | None : FlushReason
deriving Repr, BEq, DecidableEq

/-- Check if a flush is needed and determine the reason -/
def detectFlush (branchMispredicted : Bool) (exceptionOccurred : Bool) : FlushReason :=
  if branchMispredicted then
    FlushReason.BranchMisprediction
  else if exceptionOccurred then
    FlushReason.Exception
  else
    FlushReason.None

/-- Get flush target PC based on flush reason.

    Branch misprediction: Redirect to correct branch target
    Exception: Redirect to trap handler (future - for now just return target)
-/
def getFlushTargetPC (reason : FlushReason) (branchTarget : UInt32) (trapHandler : UInt32) : UInt32 :=
  match reason with
  | FlushReason.BranchMisprediction => branchTarget
  | FlushReason.Exception => trapHandler
  | FlushReason.None => 0  -- Should not be called

end Shoumei.RISCV.Control
