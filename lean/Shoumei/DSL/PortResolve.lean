/-
DSL/PortResolve.lean - Canonical Port Resolution and Wiring Validation

Provides canonical port name normalization and port resolution:
- Normalizes bracket, underscore, and bare indexed port names to a canonical PortKey.
- Resolves submodule-local wires to parent-circuit wires across CircuitInstances.
- Validates that circuits are WellWired: every instance input port is connected.
-/

import Shoumei.DSL
import Std.Data.HashMap
import Std.Data.HashSet

namespace Shoumei.DSL.PortResolve

open Shoumei

/-- Canonical form of a port key: a base name and an optional bit index.
    Examples:
    - "in0[3]", "in0_3" normalise to `⟨"in0", some 3⟩`
    - "data[31]", "data_31", "data31" normalise to `⟨"data", some 31⟩`
    - "clk", "enq_valid" normalise to `⟨"clk", none⟩`, `⟨"enq_valid", none⟩` -/
structure PortKey where
  base : String
  idx  : Option Nat
  deriving Repr, BEq, DecidableEq, Hashable

/-- Parse a port name that may contain indexing in various formats.
    Bracket:    "alloc_physRd[0]" → some ("alloc_physRd", 0)
    Underscore: "data_3"          → some ("data", 3)
    Bare:       "in0"             → some ("in", 0)
    Non-indexed:"enq_valid"       → none -/
def parsePortIndex (portName : String) : Option (String × Nat) :=
  -- Try bracket indexing first: portName[N]
  match portName.splitOn "[" with
  | [base, idxPart] =>
      let idxStr := String.ofList (idxPart.toList.takeWhile (· != ']'))
      match idxStr.toNat? with
      | some idx => some (base, idx)
      | none => none
  | _ =>
      -- Try underscore or bare suffix: extract trailing digits
      let chars := portName.toList
      let digitSuffix := chars.reverse.takeWhile Char.isDigit |>.reverse
      if digitSuffix.isEmpty then
        none
      else
        let idxStr := String.ofList digitSuffix
        let baseStr := String.ofList (chars.take (chars.length - digitSuffix.length))
        match idxStr.toNat? with
        | some idx =>
            -- Strip trailing underscores from base if present (underscore indexing)
            let baseChars := (baseStr.toList.reverse.dropWhile (· == '_')).reverse
            let base := String.ofList baseChars
            -- Don't parse if base is empty
            if base.isEmpty then none
            else some (base, idx)
        | none => none

/-- Normalise a wire or port name to its canonical PortKey representation. -/
def normalizePortKey (s : String) : PortKey :=
  match parsePortIndex s with
  | some (base, idx) => ⟨base, some idx⟩
  | none => ⟨s, none⟩

/-- Pre-indexed instance port map for kernel-reducible port resolution.
    Stores reversed port bindings so the last binding for a key wins,
    matching `HashMap.insert` semantics while remaining kernel-reducible. -/
structure InstancePortMapIndex where
  bindings : List (String × Wire) := []
  deriving Repr, Inhabited

/-- Exact string lookup in port bindings. -/
def lookupExact (bindings : List (String × Wire)) (k : String) : Option Wire :=
  match bindings.find? (fun p => p.1 == k) with
  | some (_, pw) => some pw
  | none => none

/-- Normalized PortKey lookup in port bindings. -/
def lookupPortKey (bindings : List (String × Wire)) (k : PortKey) : Option Wire :=
  match bindings.find? (fun p => normalizePortKey p.1 == k) with
  | some (_, pw) => some pw
  | none => none

/-- Build lookup index for an instance's port map. -/
def buildInstanceIndex (inst : CircuitInstance) : InstancePortMapIndex :=
  { bindings := inst.portMap.reverse }

/-- Resolve a submodule wire using a precomputed instance index. -/
def resolvePortWithIndex (sub : Circuit) (idx : InstancePortMapIndex) (w : Wire) : Option Wire :=
  -- 1. Exact string match
  match lookupExact idx.bindings w.name with
  | some parentWire => some parentWire
  | none =>
      -- 2. Direct normalized PortKey match
      match lookupPortKey idx.bindings (normalizePortKey w.name) with
      | some parentWire => some parentWire
      | none =>
          -- 3. SignalGroup match
          let sgWire := sub.signalGroups.findSome? fun (sg : SignalGroup) =>
            match sg.wires.findIdx? (· == w) with
            | some i => lookupPortKey idx.bindings (PortKey.mk sg.name (some i))
            | none => none
          match sgWire with
          | some parentWire => some parentWire
          | none =>
              -- 4. Clock alias
              if w.name == "clk" || w.name == "clock" then
                lookupExact idx.bindings "clock" <|> lookupExact idx.bindings "clk"
              -- 5. Reset alias
              else if w.name == "rst" || w.name == "reset" then
                lookupExact idx.bindings "reset" <|> lookupExact idx.bindings "rst"
              -- 6. Tied constants
              else if w.name == "zero" || w.name == "one" then
                some w
              else
                none

/-- Resolve a submodule-local wire to the parent wire an instance binds it to.
    `none` means the port is unbound. -/
def resolvePort (sub : Circuit) (inst : CircuitInstance) (w : Wire) : Option Wire :=
  resolvePortWithIndex sub (buildInstanceIndex inst) w

/-- Module registry mapping module name to Circuit definition. -/
abbrev ModuleRegistry := List (String × Circuit)

/-- Unconnected input port diagnostic for an instance. -/
structure MissingPort where
  parentModule : String
  instName     : String
  childModule  : String
  portWire     : Wire
  deriving Repr

/-- Check that every input port of an instance resolves to a parent wire.
    Returns list of missing/unconnected input ports. -/
def checkInstanceInputs (reg : ModuleRegistry) (parentName : String)
    (inst : CircuitInstance) : List MissingPort :=
  match reg.find? (fun p => p.1 == inst.moduleName) with
  | none => []  -- External/unemitted primitive (e.g. SRAM macro), skipped
  | some (_, subMod) =>
      let idx := buildInstanceIndex inst
      subMod.inputs.filterMap fun inWire =>
        match resolvePortWithIndex subMod idx inWire with
        | some _ => none
        | none => some {
            parentModule := parentName,
            instName     := inst.instName,
            childModule  := inst.moduleName,
            portWire     := inWire
          }

/-- Check that all instances in a circuit have every input port connected. -/
def checkCircuitWiring (reg : ModuleRegistry) (c : Circuit) : List MissingPort :=
  c.instances.flatMap (checkInstanceInputs reg c.name)

/-- Circuit is WellWired: every input port of every instance resolves to a parent wire. -/
def WellWired (reg : ModuleRegistry) (c : Circuit) : Bool :=
  (checkCircuitWiring reg c).isEmpty

/-- Check wiring for an entire registry of circuits.
    Returns the list of all missing input ports across all circuits. -/
def checkRegistryWiring (circuits : List Circuit) : List MissingPort :=
  let regMap : Std.HashMap String Circuit := circuits.foldl (fun m c => m.insert c.name c) {}
  circuits.flatMap fun (c : Circuit) =>
    c.instances.flatMap fun inst =>
      match regMap.get? inst.moduleName with
      | none => []
      | some (subMod : Circuit) =>
          let idx := buildInstanceIndex inst
          subMod.inputs.filterMap fun inWire =>
            match resolvePortWithIndex subMod idx inWire with
            | some _ => none
            | none => some {
                parentModule := c.name,
                instName     := inst.instName,
                childModule  := inst.moduleName,
                portWire     := inWire
              }

end Shoumei.DSL.PortResolve
