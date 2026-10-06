/-
HDL/Module.lean - High-Level RTL Module Structure

Defines the high-level RTL module definition:
- Explicit typed input and output ports
- Pipeline register declarations with clock and reset bindings
- Submodule instances with typed port maps
- DesignTarget specification for area and delay optimization
-/

import Shoumei.DSL
import Shoumei.HDL.Types
import Shoumei.HDL.Expr
import Shoumei.Components.Spec

namespace Shoumei.HDL

open Shoumei
open Shoumei.Components

/-- Port definition specifying name and bit-width. -/
structure PortDef where
  name  : String
  width : Nat
  deriving Repr, BEq, Hashable

/-- Module output binding connecting a port name to a typed signal expression. -/
inductive OutputBinding where
  | mk (name : String) (w : Nat) (expr : Signal w) : OutputBinding

/-- Submodule input binding connecting an instance port to a typed signal expression. -/
inductive InputBinding where
  | mk (portName : String) (w : Nat) (expr : Signal w) : InputBinding

/-- Internal wire binding connecting a wire name to a typed signal expression. -/
inductive WireBinding where
  | mk (name : String) (w : Nat) (expr : Signal w) : WireBinding

/-- Register definition specifying clock, reset, initial value, and next signal. -/
inductive RegBinding where
  | mk (name : String) (w : Nat) (clock reset : Wire)
       (init : BitVec w) (next : Signal w) : RegBinding

/-- High-level submodule instance binding. -/
structure InstanceBinding where
  instName   : String
  moduleName : String
  inputs     : List InputBinding
  outputs    : List (String × Nat)  -- submodule port name and bit-width
  deriving Inhabited

/-- High-level RTL module representation. -/
structure HDLModule where
  name      : String
  inputs    : List PortDef
  outputs   : List OutputBinding
  wires     : List WireBinding          := []
  registers : List RegBinding           := []
  instances : List InstanceBinding      := []
  target    : DesignTarget              := {}

namespace HDLModule

/-- Empty module helper. -/
def empty (name : String) : HDLModule := {
  name := name
  inputs := []
  outputs := []
}

/-- Add an input port to a module. -/
def addInput (m : HDLModule) (name : String) (width : Nat) : HDLModule :=
  { m with inputs := m.inputs ++ [⟨name, width⟩] }

/-- Add an internal wire binding to a module. -/
def addWire (m : HDLModule) (name : String) (width : Nat) (expr : Signal width) : HDLModule :=
  { m with wires := m.wires ++ [.mk name width expr] }

/-- Add an output port binding to a module. -/
def addOutput (m : HDLModule) (name : String) (width : Nat) (expr : Signal width) : HDLModule :=
  { m with outputs := m.outputs ++ [.mk name width expr] }

/-- Add a pipeline register to a module. -/
def addRegister (m : HDLModule) (name : String) (width : Nat) (clock reset : Wire)
    (next : Signal width) (init : BitVec width := BitVec.ofNat width 0) : HDLModule :=
  { m with registers := m.registers ++ [.mk name width clock reset init next] }

/-- Add a submodule instance to a module. -/
def addInstance (m : HDLModule) (inst : InstanceBinding) : HDLModule :=
  { m with instances := m.instances ++ [inst] }

end HDLModule

end Shoumei.HDL
