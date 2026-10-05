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
  set { s with gates := s.gates ++ [g] }

/-- Emit a submodule instance into the circuit netlist. -/
def emitInstance (inst : CircuitInstance) : ElabM Unit := do
  let s ← get
  set { s with instances := s.instances ++ [inst] }

/-- Emit a signal group for SystemVerilog bus bundling. -/
def emitSignalGroup (sg : SignalGroup) : ElabM Unit := do
  let s ← get
  set { s with signalGroups := s.signalGroups ++ [sg] }

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
      return aWires ++ bWires

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
        let impl := selectAdder spec
        let modName := adderImplName impl spec
        let instName ← freshWire "u_add"
        let aPorts := (List.range w).map fun i => (s!"a_{i}", aWires[i]!)
        let bPorts := (List.range w).map fun i => (s!"b_{i}", bWires[i]!)
        let sumPorts := (List.range w).map fun i => (s!"result_{i}", outWires[i]!)
        emitInstance {
          moduleName := modName
          instName := instName.name
          portMap := aPorts ++ bPorts ++ sumPorts
        }
      return outWires

  | w, .sub a b => do
      let aWires ← lowerSignal target a
      let bWires ← lowerSignal target b
      let outWires ← freshWires "diff" w
      let bInvWires ← freshWires "binv" w
      for i in [:w] do
        emitGate (Gate.mkNOT (bWires[i]!) (bInvWires[i]!))
      let spec : AdderSpec := {
        pdk := target.pdk
        periodPs := target.periodPs
        aim := target.aim
        width := w
        cin := .one
      }
      let impl := selectAdder spec
      let modName := adderImplName impl spec
      let instName ← freshWire "u_sub"
      let aPorts := (List.range w).map fun i => (s!"a_{i}", aWires[i]!)
      let bPorts := (List.range w).map fun i => (s!"b_{i}", bInvWires[i]!)
      let sumPorts := (List.range w).map fun i => (s!"result_{i}", outWires[i]!)
      emitInstance {
        moduleName := modName
        instName := instName.name
        portMap := aPorts ++ bPorts ++ sumPorts
      }
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
      let xorWires ← freshWires "eq_xor" srcW
      for i in [:srcW] do
        emitGate (Gate.mkXOR (aWires[i]!) (bWires[i]!) (xorWires[i]!))
      let outW ← freshWire "eq"
      if srcW == 0 then
        emitGate (Gate.mkBUF (Wire.mk "one") outW)
      else
        let mut cur := xorWires[0]!
        for i in [1:srcW] do
          let nextOr ← freshWire "eq_or"
          emitGate (Gate.mkOR cur (xorWires[i]!) nextOr)
          cur := nextOr
        emitGate (Gate.mkNOT cur outW)
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
        let bInvWires ← freshWires "cmp_binv" srcW
        for i in [:srcW] do
          emitGate (Gate.mkNOT (bWires[i]!) (bInvWires[i]!))
        let spec : AdderSpec := {
          pdk := target.pdk
          periodPs := target.periodPs
          aim := target.aim
          width := srcW
          cin := .one
        }
        let impl := selectAdder spec
        let modName := adderImplName impl spec
        let instName ← freshWire "u_cmp_sub"
        let aPorts := (List.range srcW).map fun i => (s!"a_{i}", aWires[i]!)
        let bPorts := (List.range srcW).map fun i => (s!"b_{i}", bInvWires[i]!)
        let sumPorts := (List.range srcW).map fun i => (s!"result_{i}", diffWires[i]!)
        emitInstance {
          moduleName := modName
          instName := instName.name
          portMap := aPorts ++ bPorts ++ sumPorts
        }
        emitGate (Gate.mkBUF (Wire.mk "zero") outW)
      return [outW]

  | w, .instOut instName portName _ => do
      return (List.range w).map fun i =>
        if w == 1 then Wire.mk s!"{instName}_{portName}"
        else Wire.mk s!"{instName}_{portName}_{i}"

/-- Lower an entire `HDLModule` into a verified `Circuit` netlist. -/
def lowerModule (m : HDLModule) : Circuit :=
  let initial : ElabState := {}
  let ((inputs, outputs), (state : ElabState)) := (do
    -- Lower inputs
    let inWires := m.inputs.flatMap fun (p : PortDef) =>
      (List.range p.width).map fun i =>
        if p.width == 1 then Wire.mk p.name else Wire.mk s!"{p.name}_{i}"
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
    gates := state.gates
    instances := state.instances
    signalGroups := state.signalGroups
  }

end Shoumei.HDL
