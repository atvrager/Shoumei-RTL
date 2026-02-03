/-
DSL/Interfaces.lean - Canonical Interface Bundle Definitions

Shared interface types for Shoumei codegen v2. These define the standard
bundles (Decoupled, operand, CDB, register port) used across RISC-V modules.

Codegen reads these to emit proper Chisel Bundles and SV structs.
-/

import Shoumei.DSL

namespace Shoumei.DSL.Interfaces

open Shoumei

/-! ## Canonical Bundles -/

/-- Decoupled (ready/valid) interface bundle.
    Fields: bits (UInt width), valid (Bool), ready (Bool).
    Protocol tag enables codegen to emit Chisel `Decoupled` wrappers. -/
def decoupledBundle (width : Nat) : InterfaceBundle := {
  name := "decoupled"
  signals := [("bits", .UInt width), ("valid", .Bool), ("ready", .Bool)]
  protocol := some "decoupled"
}

/-- Operand bundle for reservation station entries.
    Fields: ready (Bool), tag (UInt 6), data (UInt 32). -/
def operandBundle : InterfaceBundle := {
  name := "operand"
  signals := [("ready", .Bool), ("tag", .UInt 6), ("data", .UInt 32)]
}

/-- Common Data Bus entry bundle.
    Fields: tag (UInt 6), data (UInt 32). -/
def cdbEntryBundle : InterfaceBundle := {
  name := "cdb_entry"
  signals := [("tag", .UInt 6), ("data", .UInt 32)]
}

/-- Register write port bundle (parameterized address/data widths).
    Fields: en (Bool), addr (UInt addrW), data (UInt dataW). -/
def regWriteBundle (addrW dataW : Nat) : InterfaceBundle := {
  name := "reg_write"
  signals := [("en", .Bool), ("addr", .UInt addrW), ("data", .UInt dataW)]
}

/-- Register read port bundle (parameterized address/data widths).
    Fields: addr (UInt addrW), data (UInt dataW). -/
def regReadBundle (addrW dataW : Nat) : InterfaceBundle := {
  name := "reg_read"
  signals := [("addr", .UInt addrW), ("data", .UInt dataW)]
}

/-! ## Wire-name helpers -/

/-- Generate a list of indexed wires: name_0, name_1, ..., name_{n-1}. -/
def makeIndexedWires (name : String) (n : Nat) : List Wire :=
  (List.range n).map (fun i => Wire.mk s!"{name}_{i}")

end Shoumei.DSL.Interfaces
