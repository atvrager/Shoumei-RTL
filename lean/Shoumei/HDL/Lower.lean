/-
HDL/Lower.lean - Lowering Engine from High-Level RTL DSL to Netlist Circuit

Translates high-level `HDLModule` definitions to verified `Circuit` netlists:
- Allocates unique internal wire names using a state monad
- Translates expressions to basic logic gates (AND, OR, NOT, XOR, MUX)
- Lowers multi-bit addition and subtraction to verified leaf adders
- Maps register definitions to DFlipFlop sequential gates
- Automatically generates SignalGroup bus annotations for SystemVerilog
-/

import Shoumei.DSL
import Shoumei.HDL.Types
import Shoumei.HDL.Expr
import Shoumei.HDL.Module
import Shoumei.Components.Spec
import Shoumei.Components.Select
import Shoumei.Components.AdderLibrary

namespace Shoumei.HDL

open Shoumei
open Shoumei.Components

/-- Internal elaboration state during lowering. -/
structure ElabState where
  nextWireId   : Nat := 0
  gates        : List Gate := []
  instances    : List CircuitInstance := []
  signalGroups : List SignalGroup := []

/-- Elaboration monad for lowering high-level hardware AST. -/
abbrev ElabM := StateM ElabState

/-- Generate a fresh unique wire identifier. -/
def freshWire (pfx : String := "w") : ElabM Wire := do
  let s ← get
  set { s with nextWireId := s.nextWireId + 1 }
  return Wire.mk s!"{pfx}_{s.nextWireId}"

/-- Generate `w` fresh unique wire identifiers. -/
def freshWires (pfx : String) (w : Nat) : ElabM (List Wire) := do
  (List.range w).mapM fun _ => freshWire pfx

/-- Emit a gate into the circuit netlist. -/
def emitGate (g : Gate) : ElabM Unit := do
  let s ← get
  set { s with gates := g :: s.gates }

/-- Emit a submodule instance into the circuit netlist. -/
def emitInstance (inst : CircuitInstance) : ElabM Unit := do
  let s ← get
  set { s with instances := inst :: s.instances }

/-- Emit a signal group for SystemVerilog bus bundling. -/
def emitSignalGroup (sg : SignalGroup) : ElabM Unit := do
  let s ← get
  set { s with signalGroups := sg :: s.signalGroups }

/-- Construct a balanced binary OR tree to reduce a list of wires to a single wire. -/
partial def lowerOrTree (pfx : String) (wires : List Wire) : ElabM Wire := do
  match wires with
  | [] => return Wire.mk "zero"
  | [w] => return w
  | _ =>
      let mut nextLevel : List Wire := []
      let mut i := 0
      let mut pairIdx := 0
      while i < wires.length do
        if i + 1 < wires.length then
          let outW ← freshWire s!"{pfx}_{pairIdx}"
          emitGate (Gate.mkOR (wires[i]!) (wires[i + 1]!) outW)
          nextLevel := outW :: nextLevel
          i := i + 2
          pairIdx := pairIdx + 1
        else
          nextLevel := (wires[i]!) :: nextLevel
          i := i + 1
      lowerOrTree s!"{pfx}_l" nextLevel.reverse

/-- Lower a typed signal expression to a list of hardware wires. -/
def lowerSignal (target : DesignTarget) : {w : Nat} → Signal w → ElabM (List Wire)
  | w, .const val => do
      let wires ← freshWires "c" w
      for i in [:w] do
        let bitVal := val.getLsbD i
        let outW := wires[i]!
        if bitVal then
          emitGate (Gate.mkBUF (Wire.mk "one") outW)
        else
          emitGate (Gate.mkBUF (Wire.mk "zero") outW)
      return wires

  | w, .input name _ => do
      return (List.range w).map fun i =>
        if w == 1 then Wire.mk name else Wire.mk s!"{name}_{i}"

  | w, .wire name _ => do
      return (List.range w).map fun i =>
        if w == 1 then Wire.mk name else Wire.mk s!"{name}_{i}"

  | w, .reg name _ clock reset _init next => do
      let nextWires ← lowerSignal target next
      let qWires := (List.range w).map fun i =>
        if w == 1 then Wire.mk name else Wire.mk s!"{name}_{i}"
      for i in [:w] do
        emitGate (Gate.mkDFF (nextWires[i]!) clock reset (qWires[i]!))
      if w > 1 then
        emitSignalGroup { name := name, width := w, wires := qWires }
      return qWires

  | _, .extract src hi lo => do
      let srcWires ← lowerSignal target src
      let len := hi - lo + 1
      return (List.range len).map fun i => srcWires[(lo + i)]!

  | _, .concat a b => do
      let aWires ← lowerSignal target a
      let bWires ← lowerSignal target b
      return bWires ++ aWires

  | w, .not a => do
      let aWires ← lowerSignal target a
      let outWires ← freshWires "not" w
      for i in [:w] do
        emitGate (Gate.mkNOT (aWires[i]!) (outWires[i]!))
      return outWires

  | w, .and a b => do
      let aWires ← lowerSignal target a
      let bWires ← lowerSignal target b
      let outWires ← freshWires "and" w
      for i in [:w] do
        emitGate (Gate.mkAND (aWires[i]!) (bWires[i]!) (outWires[i]!))
      return outWires

  | w, .or a b => do
      let aWires ← lowerSignal target a
      let bWires ← lowerSignal target b
      let outWires ← freshWires "or" w
      for i in [:w] do
        emitGate (Gate.mkOR (aWires[i]!) (bWires[i]!) (outWires[i]!))
      return outWires

  | w, .xor a b => do
      let aWires ← lowerSignal target a
      let bWires ← lowerSignal target b
      let outWires ← freshWires "xor" w
      for i in [:w] do
        emitGate (Gate.mkXOR (aWires[i]!) (bWires[i]!) (outWires[i]!))
      return outWires

  | w, .mux sel thenSig elseSig => do
      let selWires ← lowerSignal target sel
      let thenWires ← lowerSignal target thenSig
      let elseWires ← lowerSignal target elseSig
      let selW := selWires[0]!
      let outWires ← freshWires "mux" w
      for i in [:w] do
        emitGate (Gate.mkMUX (elseWires[i]!) (thenWires[i]!) selW (outWires[i]!))
      return outWires

  | w, .add a b => do
      let aWires ← lowerSignal target a
      let bWires ← lowerSignal target b
      let outWires ← freshWires "sum" w
      if w == 1 then
        emitGate (Gate.mkXOR (aWires[0]!) (bWires[0]!) (outWires[0]!))
      else
        let spec : AdderSpec := {
          pdk := target.pdk
          periodPs := target.periodPs
          aim := target.aim
          width := w
          cin := .none
        }
        if w == 32 || w == 64 || w == 106 then
          let impl := selectAdder spec
          let modName := adderImplName impl spec
          let instName ← freshWire "u_add"
          let aPorts := (List.range w).map fun i => (s!"a_{i}", aWires[i]!)
          let bPorts := (List.range w).map fun i => (s!"b_{i}", bWires[i]!)
          let sumPorts := (List.range w).map fun i => (s!"sum_{i}", outWires[i]!)
          emitInstance {
            moduleName := modName
            instName := instName.name
            portMap := aPorts ++ bPorts ++ sumPorts
          }
        else
          let pfx ← freshWire "add"
          let (gates, _) := mkAddFor spec aWires bWires (Wire.mk "zero") outWires pfx.name
          for g in gates do emitGate g
      return outWires

  | w, .sub a b => do
      let aWires ← lowerSignal target a
      let bWires ← lowerSignal target b
      let outWires ← freshWires "diff" w
      let spec : AdderSpec := {
        pdk := target.pdk
        periodPs := target.periodPs
        aim := target.aim
        width := w
        cin := .one
      }
      if w == 32 || w == 64 || w == 106 then
        let bInvWires ← freshWires "binv" w
        for i in [:w] do
          emitGate (Gate.mkNOT (bWires[i]!) (bInvWires[i]!))
        let impl := selectAdder spec
        let modName := adderImplName impl spec
        let instName ← freshWire "u_sub"
        let aPorts := (List.range w).map fun i => (s!"a_{i}", aWires[i]!)
        let bPorts := (List.range w).map fun i => (s!"b_{i}", bInvWires[i]!)
        let sumPorts := (List.range w).map fun i => (s!"sum_{i}", outWires[i]!)
        emitInstance {
          moduleName := modName
          instName := instName.name
          portMap := aPorts ++ bPorts ++ sumPorts
        }
      else
        let pfx ← freshWire "sub"
        let (gates, _) := mkSubFor spec aWires bWires outWires pfx.name (Wire.mk "one")
        for g in gates do emitGate g
      return outWires

  | _, .mul a b => do
      let aWires ← lowerSignal target a
      let bWires ← lowerSignal target b
      let totalW := aWires.length + bWires.length
      let outWires ← freshWires "mul" totalW
      return outWires

  | _, .eq a b => do
      let aWires ← lowerSignal target a
      let bWires ← lowerSignal target b
      let srcW := aWires.length
      let xorWires ← freshWires "diff" srcW
      for i in [:srcW] do
        emitGate (Gate.mkXOR (aWires[i]!) (bWires[i]!) (xorWires[i]!))
      let outW ← freshWire "eq"
      if srcW == 0 then
        emitGate (Gate.mkBUF (Wire.mk "one") outW)
      else
        let anyDiff ← lowerOrTree "or_tree" xorWires
        emitGate (Gate.mkNOT anyDiff outW)
      return [outW]

  | _, .ult a b => do
      let aWires ← lowerSignal target a
      let bWires ← lowerSignal target b
      let srcW := aWires.length
      let outW ← freshWire "ult"
      if srcW == 0 then
        emitGate (Gate.mkBUF (Wire.mk "zero") outW)
      else
        let diffWires ← freshWires "cmp_diff" srcW
        let spec : AdderSpec := {
          pdk := target.pdk
          periodPs := target.periodPs
          aim := target.aim
          width := srcW
          cin := .one
        }
        let pfx ← freshWire "cmp"
        let (gates, borrow) := mkSubFor spec aWires bWires diffWires pfx.name (Wire.mk "one")
        for g in gates do emitGate g
        emitGate (Gate.mkBUF borrow outW)
      return [outW]

  | w, .instOut instName portName _ => do
      return (List.range w).map fun i =>
        if w == 1 then Wire.mk s!"{instName}_{portName}"
        else Wire.mk s!"{instName}_{portName}_{i}"

  | w, .dshr s amt => do
      let sWires ← lowerSignal target s
      let amtWires ← lowerSignal target amt
      let mut curWires := sWires
      for stage in [:amtWires.length] do
        let shiftVal := Nat.pow 2 stage
        let nextWires ← freshWires s!"dshr_s{stage}" w
        let bitW := amtWires[stage]!
        for i in [:w] do
          let shiftedW := if i + shiftVal < w then curWires[i + shiftVal]! else Wire.mk "zero"
          emitGate (Gate.mkMUX (curWires[i]!) shiftedW bitW (nextWires[i]!))
        curWires := nextWires
      return curWires

  | w, .dshl s amt => do
      let sWires ← lowerSignal target s
      let amtWires ← lowerSignal target amt
      let mut curWires := sWires
      for stage in [:amtWires.length] do
        let shiftVal := Nat.pow 2 stage
        let nextWires ← freshWires s!"dshl_s{stage}" w
        let bitW := amtWires[stage]!
        for i in [:w] do
          let shiftedW := if i ≥ shiftVal then curWires[i - shiftVal]! else Wire.mk "zero"
          emitGate (Gate.mkMUX (curWires[i]!) shiftedW bitW (nextWires[i]!))
        curWires := nextWires
      return curWires

/-- Lower an entire `HDLModule` into a verified `Circuit` netlist. -/
def lowerModule (m : HDLModule) : Circuit :=
  let initial : ElabState := {}
  let ((inputs, outputs), (state : ElabState)) := (do
    -- Lower inputs
    let mut inWires : List Wire := []
    for (p : PortDef) in m.inputs do
      let pWires := (List.range p.width).map fun i =>
        if p.width == 1 then Wire.mk p.name else Wire.mk s!"{p.name}_{i}"
      inWires := inWires ++ pWires
      if p.width > 1 then
        emitSignalGroup { name := p.name, width := p.width, wires := pWires }
    -- Lower registers
    for reg in m.registers do
      match reg with
      | RegBinding.mk rname rw clock reset init next =>
          let _ ← lowerSignal m.target (.reg rname rw clock reset init next)
    -- Lower instances
    for inst in m.instances do
      let mut pMap : List (String × Wire) := []
      for inb in inst.inputs do
        match inb with
        | InputBinding.mk pname pw pexpr =>
            let pWires ← lowerSignal m.target pexpr
            for i in [:pw] do
              let portKey := if pw == 1 then pname else s!"{pname}_{i}"
              pMap := pMap ++ [(portKey, pWires[i]!)]
      for (outName, outW) in inst.outputs do
        for i in [:outW] do
          let portKey := if outW == 1 then outName else s!"{outName}_{i}"
          let localW := Wire.mk s!"{inst.instName}_{portKey}"
          pMap := pMap ++ [(portKey, localW)]
      emitInstance {
        moduleName := inst.moduleName
        instName := inst.instName
        portMap := pMap
      }
    -- Lower outputs
    let mut outWires : List Wire := []
    for outb in m.outputs do
      match outb with
      | OutputBinding.mk oname ow oexpr =>
          let exprWires ← lowerSignal m.target oexpr
          let destWires := (List.range ow).map fun i =>
            if ow == 1 then Wire.mk oname else Wire.mk s!"{oname}_{i}"
          for i in [:ow] do
            emitGate (Gate.mkBUF (exprWires[i]!) (destWires[i]!))
          outWires := outWires ++ destWires
          if ow > 1 then
            emitSignalGroup { name := oname, width := ow, wires := destWires }
    return (inWires, outWires)
  ).run initial

  {
    name := m.name
    inputs := inputs
    outputs := outputs
    gates := state.gates.reverse
    instances := state.instances.reverse
    signalGroups := state.signalGroups.reverse
  }

end Shoumei.HDL
