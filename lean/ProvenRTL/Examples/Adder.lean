/-
Examples/Adder.lean - Full Adder Circuit Example

A full adder adds three single-bit inputs (a, b, cin) and produces
a sum bit and a carry-out bit (cout).

Truth table:
a b cin | sum cout
--------|----------
0 0 0   | 0   0
0 0 1   | 1   0
0 1 0   | 1   0
0 1 1   | 0   1
1 0 0   | 1   0
1 0 1   | 0   1
1 1 0   | 0   1
1 1 1   | 1   1

Logic:
  sum  = a ⊕ b ⊕ cin
  cout = (a ∧ b) ∨ (cin ∧ (a ⊕ b))
-/

import ProvenRTL.DSL
import ProvenRTL.Semantics
import ProvenRTL.Codegen.SystemVerilog
import ProvenRTL.Codegen.Chisel

namespace ProvenRTL.Examples

-- Define the full adder circuit
def fullAdderCircuit : Circuit :=
  let a := Wire.mk "a"
  let b := Wire.mk "b"
  let cin := Wire.mk "cin"
  let sum := Wire.mk "sum"
  let cout := Wire.mk "cout"

  -- Internal wires
  let ab_xor := Wire.mk "ab_xor"      -- a ⊕ b
  let ab_and := Wire.mk "ab_and"      -- a ∧ b
  let cin_ab := Wire.mk "cin_ab"      -- cin ∧ (a ⊕ b)

  { name := "FullAdder"
    inputs := [a, b, cin]
    outputs := [sum, cout]
    gates := [
      -- sum = a ⊕ b ⊕ cin
      Gate.mkXOR a b ab_xor,           -- ab_xor = a ⊕ b
      Gate.mkXOR ab_xor cin sum,       -- sum = ab_xor ⊕ cin

      -- cout = (a ∧ b) ∨ (cin ∧ (a ⊕ b))
      Gate.mkAND a b ab_and,           -- ab_and = a ∧ b
      Gate.mkAND cin ab_xor cin_ab,    -- cin_ab = cin ∧ ab_xor
      Gate.mkOR ab_and cin_ab cout     -- cout = ab_and ∨ cin_ab
    ]
  }

-- Generate SystemVerilog for the full adder
def generateSystemVerilog : String :=
  Codegen.SystemVerilog.toSystemVerilog fullAdderCircuit

-- Generate Chisel for the full adder
def generateChisel : String :=
  Codegen.Chisel.toChisel fullAdderCircuit

-- Write SystemVerilog to file
def writeSystemVerilog : IO Unit := do
  let sv := generateSystemVerilog
  let path := "output/sv-from-lean/FullAdder.sv"
  IO.FS.writeFile path sv
  IO.println s!"✓ Generated: {path}"

-- Write Chisel to file
def writeChisel : IO Unit := do
  let chisel := generateChisel
  let path := "chisel/src/main/scala/generated/FullAdder.scala"
  IO.FS.writeFile path chisel
  IO.println s!"✓ Generated: {path}"

-- Main entry point for code generation
def main : IO Unit := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "  証明 Shoumei RTL - Code Generation"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println ""
  IO.println "Generating code for FullAdder circuit..."
  IO.println ""
  writeSystemVerilog
  writeChisel
  IO.println ""
  IO.println "✓ Code generation complete"

-- TODO: Add test cases that verify the circuit against the truth table
-- def test_fullAdder : IO Unit := ...

end ProvenRTL.Examples
