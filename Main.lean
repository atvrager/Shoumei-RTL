/-
Main.lean - Code Generation Entry Point

This is the main entry point for the codegen executable.
It calls the code generation functions from Examples.Adder.
-/

import ProvenRTL.Examples.Adder

def main : IO Unit := ProvenRTL.Examples.main
