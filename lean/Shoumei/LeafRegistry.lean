/-
LeafRegistry.lean - Circuit Registry for Leaf Subsystems

Maintains the circuit lists for foundation, combinational, and sequential subsystems.
These leaf subsystems do not depend on the CPU, microcode, caches, or SoC.
-/

import Shoumei.DSL
import Shoumei.Components.Select

-- Phase 0: Foundation
import Shoumei.Examples.Adder
import Shoumei.Circuits.Sequential.DFF
import Shoumei.Circuits.Sequential.Queue

-- Phase 1: Arithmetic Building Blocks
import Shoumei.Circuits.Combinational.PCIncrementer
import Shoumei.Circuits.Combinational.BranchTargetAdder
import Shoumei.Circuits.Combinational.RippleCarryAdder
import Shoumei.Circuits.Combinational.Subtractor
import Shoumei.Circuits.Combinational.Comparator
import Shoumei.Circuits.Combinational.LogicUnit
import Shoumei.Circuits.Combinational.Shifter
import Shoumei.Circuits.Combinational.ALU
import Shoumei.Circuits.Combinational.KoggeStoneAdder

-- Phase 2: Decoders and Muxes
import Shoumei.Circuits.Combinational.Decoder
import Shoumei.Circuits.Combinational.MuxTree
import Shoumei.Circuits.Combinational.Arbiter
import Shoumei.Circuits.Combinational.OneHotEncoder
import Shoumei.Circuits.Combinational.Popcount

-- Phase 3: Sequential Components
import Shoumei.Circuits.Sequential.QueueN
import Shoumei.Circuits.Sequential.QueueComponents
import Shoumei.Circuits.Sequential.Register

namespace Shoumei.LeafRegistry

open Shoumei
open Shoumei.Components
open Shoumei.Examples
open Shoumei.Circuits.Combinational
open Shoumei.Circuits.Sequential

def foundationBaseCircuits : List Circuit := [
  dff,
  fullAdderCircuit,
  mkRippleCarryAdder4,
  mkLogicUnit4,
  mkMux4x1,
  mkComparator4,
  q1w1,
  mkQueue1StructuralComplete 8,
  mkQueue1FlowStructural 39,
  mkQueue1FlowStructural 70,
  mkQueue1FlowStructural 71,
  mkQueue1FlowStructural 72,
  mkQueue1FlowStructural 103,
  mkQueue1FlowStructural 104,
  mkQueue1FlowStructural 43,
  mkQueue1FlowStructural 44,
  mkQueue1FlowStructural 75,
  mkQueue1FlowStructural 76
]

def combinationalCircuits : List Circuit := [
  pcIncrementer4Circuit,
  pcIncrementer8Circuit,
  branchTargetAdder32Circuit,
  mkKoggeStoneAdder32,
  mkKoggeStoneAdder32NoCin,
  mkSubtractor32,
  mkComparator32,
  mkLogicUnit32,
  mkShifter32,
  mkALU32,
  mkDecoder 2,
  mkDecoder 3,
  mkDecoder 4,
  mkDecoder 5,
  mkDecoder 6,
  mkDecoder 7,
  mkComparatorN 6,
  mkEqualityComparatorN 6,
  mkEqualityComparator32,
  mkEqualityComparator64,
  mkMuxTree 4 32,
  mkMuxTree 4 64,
  mkMuxTree 8 2,
  mkMux8x32Hierarchical,
  mkMux8x64Hierarchical,
  mkMuxTree 16 5,
  mkMuxTree 16 6,
  mkMuxTree 16 32,
  mkMux32x6,
  mkMux64x32Hierarchical,
  mkMux64x64Hierarchical,
  mkMuxTree 64 5,
  mkPriorityArbiter2,
  mkPriorityArbiter8,
  mkPriorityArbiter64,
  mkOneHotEncoder64,
  mkPopcount8
]

def sequentialCircuits : List Circuit := [
  mkQueuePointer 3,
  mkQueuePointerLoadable 3,
  mkQueueCounterLoadable 4,
  mkRegisterN 1,
  mkRegisterN 2,
  mkRegisterN 3,
  mkRegisterN 4,
  mkRegisterN 6,
  mkRegisterN 8,
  mkRegisterN 12,
  mkRegisterN 16,
  mkRegisterN 5,
  mkRegisterN 24,
  mkRegisterN 32,
  mkRegisterN 64,
  mkRegisterEnN 1,
  mkRegisterEnN 2,
  mkRegisterEnN 4,
  mkRegisterEnN 8,
  mkRegisterEnN 16,
  mkRegisterEnN 32,
  mkRegisterEnN 64,
  mkRegisterNHierarchical 96,
  mkRegisterNHierarchical 98,
  mkRegisterNHierarchical 130,
  mkRegisterNHierarchical 157,
  mkRegisterNHierarchical 158,
  mkRegisterNHierarchical 159,
  mkRegisterNHierarchical 160,
  mkRegister160Flat
]

def leafCircuits : List Circuit :=
  (allAdderCircuits ++ foundationBaseCircuits ++ combinationalCircuits ++ sequentialCircuits).foldl
    (fun acc c => if acc.any (fun c' => c'.name == c.name) then acc else acc ++ [c]) []

def leafSubsystemCircuitNames (subsystem : String) : Option (List String) :=
  let adderNames := allAdderCircuits.map (·.name)
  match subsystem with
  | "foundation" | "base" => some (adderNames ++ foundationBaseCircuits.map (·.name))
  | "combinational"       =>
    some (combinationalCircuits.filter (fun c => !adderNames.contains c.name) |>.map (·.name))
  | "sequential"          => some (sequentialCircuits.map (·.name))
  | "all"                 => some (leafCircuits.map (·.name))
  | _                     => none

def leafCircuitsForSubsystem (subsystem : String) : Option (List Circuit) :=
  match leafSubsystemCircuitNames subsystem with
  | some names => some (leafCircuits.filter (fun c => names.contains c.name))
  | none => none

end Shoumei.LeafRegistry
