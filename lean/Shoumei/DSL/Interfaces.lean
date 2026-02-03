/-
DSL/Interfaces.lean - Canonical Interface Type Library

Defines the standard interface shapes used across the Shoumei RTL project.
These are used by codegen to emit proper Chisel Bundles, SV struct types,
and readable port groupings.

Each definition here is a factory for InterfaceBundle -- it creates the
annotation metadata, not the actual wires. Circuit definitions reference
these to declare their port semantics.

Common shapes:
  1. Decoupled (ready/valid handshake): bits[W-1:0], valid, ready
  2. Operand bundle: ready, tag[5:0], data[31:0]
  3. CDB entry: tag[5:0], data[31:0]
  4. Register write port: en, addr[N-1:0], data[W-1:0]
  5. Register read port: addr[N-1:0], data[W-1:0]
-/

import Shoumei.DSL

namespace Shoumei.DSL.Interfaces

open Shoumei

/-! ## Standard Interface Bundles -/

/-- Decoupled (ready/valid handshake) interface.
    Ports: bits[width-1:0], valid, ready -/
def decoupledBundle (width : Nat) : InterfaceBundle :=
  { name := "decoupled"
    signals := [("bits", .UInt width), ("valid", .Bool), ("ready", .Bool)]
    protocol := some "decoupled" }

/-- Operand bundle for reservation station source operands.
    Ports: ready, tag[5:0], data[31:0] -/
def operandBundle : InterfaceBundle :=
  { name := "operand"
    signals := [("ready", .Bool), ("tag", .UInt 6), ("data", .UInt 32)] }

/-- CDB (Common Data Bus) broadcast entry.
    Ports: tag[5:0], data[31:0] -/
def cdbEntryBundle : InterfaceBundle :=
  { name := "cdb_entry"
    signals := [("tag", .UInt 6), ("data", .UInt 32)] }

/-- Register write port.
    Ports: en, addr[addrW-1:0], data[dataW-1:0] -/
def regWriteBundle (addrW dataW : Nat) : InterfaceBundle :=
  { name := "reg_write"
    signals := [("en", .Bool), ("addr", .UInt addrW), ("data", .UInt dataW)]
    protocol := some "regwrite" }

/-- Register read port.
    Ports: addr[addrW-1:0], data[dataW-1:0] -/
def regReadBundle (addrW dataW : Nat) : InterfaceBundle :=
  { name := "reg_read"
    signals := [("addr", .UInt addrW), ("data", .UInt dataW)]
    protocol := some "regread" }

/-- Dispatch entry for reservation station.
    Full RS entry: opcode, dest_tag, src1 operand, src2 operand -/
def dispatchEntryBundle (opcodeW tagW dataW : Nat) : InterfaceBundle :=
  { name := "dispatch_entry"
    signals := [
      ("opcode", .UInt opcodeW),
      ("dest_tag", .UInt tagW),
      ("src1_ready", .Bool), ("src1_tag", .UInt tagW), ("src1_data", .UInt dataW),
      ("src2_ready", .Bool), ("src2_tag", .UInt tagW), ("src2_data", .UInt dataW)
    ] }

/-- Issue output from reservation station.
    Ports: opcode, dest_tag, src1_data, src2_data -/
def issueOutputBundle (opcodeW tagW dataW : Nat) : InterfaceBundle :=
  { name := "issue_output"
    signals := [
      ("opcode", .UInt opcodeW),
      ("dest_tag", .UInt tagW),
      ("src1_data", .UInt dataW),
      ("src2_data", .UInt dataW)
    ] }

/-- ALU interface: two operands + opcode → result.
    Input side: a[W-1:0], b[W-1:0], op[opW-1:0]
    Output side: result[W-1:0] -/
def aluInputBundle (dataW opW : Nat) : InterfaceBundle :=
  { name := "alu_input"
    signals := [("a", .UInt dataW), ("b", .UInt dataW), ("op", .UInt opW)] }

def aluOutputBundle (dataW : Nat) : InterfaceBundle :=
  { name := "alu_output"
    signals := [("result", .UInt dataW)] }

end Shoumei.DSL.Interfaces
