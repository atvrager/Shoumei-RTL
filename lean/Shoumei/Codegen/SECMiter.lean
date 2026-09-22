/-
Codegen/SECMiter.lean - Sequential Equivalence Checking (SEC) Miter and Script Generator

Generates:
1. Dual-instance SystemVerilog Miter modules connecting golden (reference) and
   revised (implementation) circuits, with output equivalence assertions.
2. Synopsys Formality verification TCL scripts for signoff equivalence checking.
3. Open-source Yosys verification TCL scripts (miter + sat).
4. Synopsys VC Formal verification TCL scripts.
-/

import Shoumei.DSL
import Shoumei.Codegen.Common
import Shoumei.Codegen.SystemVerilog

namespace Shoumei.Codegen.SECMiter

open Shoumei
open Shoumei.Codegen
open Shoumei.Codegen.SystemVerilog

/-- Generate a SystemVerilog SEC Miter module comparing two congruent circuits. -/
def generateSECMiter (gold rev : Circuit) (miterName : String := s!"{gold.name}_vs_{rev.name}_sec_miter") : String :=
  let ctxGold := mkContext gold
  let clkName := (ctxGold.clockWires.head?.map (·.name)).getD "clock"
  let rstName := (ctxGold.resetWires.head?.map (·.name)).getD "reset"

  -- Determine input port declarations (from gold, excluding clk and rst)
  let inputPorts := ctxGold.allSignalGroups.filter (fun sg =>
    gold.inputs.any (fun w => sg.wires.any (fun sw => sw.name == w.name)))
  let inputPortDecls := inputPorts.map (fun sg =>
    if sg.width == 1 then s!"  input logic {sg.name},"
    else s!"  input logic [{sg.width - 1}:0] {sg.name},"
  )

  -- Determine output signal groups
  let outputGroups := ctxGold.allSignalGroups.filter (fun sg =>
    gold.outputs.any (fun w => sg.wires.any (fun sw => sw.name == w.name)))

  -- Internal wire declarations for gold and rev outputs
  let goldOutputDecls := outputGroups.map (fun sg =>
    if sg.width == 1 then s!"  logic gold_{sg.name};"
    else s!"  logic [{sg.width - 1}:0] gold_{sg.name};"
  )
  let revOutputDecls := outputGroups.map (fun sg =>
    if sg.width == 1 then s!"  logic rev_{sg.name};"
    else s!"  logic [{sg.width - 1}:0] rev_{sg.name};"
  )

  -- Port connections for gold and rev instances
  let goldPortConns := [s!".{clkName}({clkName})", s!".{rstName}({rstName})"] ++
    inputPorts.map (fun sg => s!".{sg.name}({sg.name})") ++
    outputGroups.map (fun sg => s!".{sg.name}(gold_{sg.name})")

  let revPortConns := [s!".{clkName}({clkName})", s!".{rstName}({rstName})"] ++
    inputPorts.map (fun sg => s!".{sg.name}({sg.name})") ++
    outputGroups.map (fun sg => s!".{sg.name}(rev_{sg.name})")

  -- Mismatch detection
  let mismatchExprs := outputGroups.map (fun sg => s!"(gold_{sg.name} != rev_{sg.name})")
  let combinedMismatch := if mismatchExprs.isEmpty then "1'b0" else String.intercalate " || " mismatchExprs

  -- SVA properties
  let svaAssertions := outputGroups.enum.map (fun (i, sg) =>
    s!"  // Formal SEC Property: {sg.name} output equivalence\n" ++
    s!"  property p_sec_equiv_{sg.name}_{i};\n" ++
    s!"    @(posedge {clkName}) disable iff ({rstName})\n" ++
    s!"    gold_{sg.name} == rev_{sg.name};\n" ++
    s!"  endproperty\n" ++
    s!"  assert_sec_equiv_{sg.name}_{i}: assert property (p_sec_equiv_{sg.name}_{i});\n"
  )

  let header := s!"// Auto-generated SEC Miter by Shoumei Codegen\n" ++
    s!"// Golden Reference: {gold.name}\n" ++
    s!"// Revised Target:   {rev.name}\n\n" ++
    s!"module {miterName} (\n" ++
    s!"  input logic {clkName},\n" ++
    s!"  input logic {rstName},\n" ++
    String.intercalate "\n" inputPortDecls ++ "\n" ++
    s!"  output logic sec_mismatch\n" ++
    s!");\n\n"

  let internalSignals := String.intercalate "\n" (goldOutputDecls ++ revOutputDecls) ++ "\n\n"

  let instGold := s!"  // Golden Reference Instance\n" ++
    s!"  {gold.name} u_gold (\n" ++
    s!"    " ++ String.intercalate ",\n    " goldPortConns ++ "\n" ++
    s!"  );\n\n"

  let instRev := s!"  // Revised Implementation Instance\n" ++
    s!"  {rev.name} u_rev (\n" ++
    s!"    " ++ String.intercalate ",\n    " revPortConns ++ "\n" ++
    s!"  );\n\n"

  let mismatchLogic := s!"  // Combinational Mismatch Flag\n" ++
    s!"  always_comb begin\n" ++
    s!"    sec_mismatch = {combinedMismatch};\n" ++
    s!"  end\n\n"

  let svaBlock :=
    s!"`ifdef FORMAL\n" ++
    s!"  `define SHOUMEI_FORMAL_ASSERT\n" ++
    s!"`elsif SYNTHESIS\n" ++
    s!"  // Synthesis without FORMAL: exclude assertions\n" ++
    s!"`else\n" ++
    s!"  `define SHOUMEI_FORMAL_ASSERT\n" ++
    s!"`endif\n\n" ++
    s!"`ifdef SHOUMEI_FORMAL_ASSERT\n" ++
    s!"  // --------------------------------------------------------------------------\n" ++
    s!"  // Formal Sequential Equivalence Assertions\n" ++
    s!"  // --------------------------------------------------------------------------\n" ++
    String.intercalate "\n" svaAssertions ++ "\n" ++
    s!"  `undef SHOUMEI_FORMAL_ASSERT\n" ++
    s!"`endif\n\n"

  header ++ internalSignals ++ instGold ++ instRev ++ mismatchLogic ++ svaBlock ++ "endmodule\n"

/-- Generate Synopsys Formality verification TCL script. -/
def generateFormalityTcl (goldName revName : String) (goldFiles revFiles : List String) : String :=
  let toBasename (f : String) : String := ((System.FilePath.mk f).fileName).getD f
  let goldFilesStr := String.intercalate " " (goldFiles.map toBasename)
  let revFilesStr := String.intercalate " " (revFiles.map toBasename)
  "# Synopsys Formality Equivalence Checking Script\n" ++
  "# Generated by Shoumei Codegen\n\n" ++
  "set synopsys_auto_setup true\n" ++
  "set search_path \". output/sv-from-lean $search_path\"\n\n" ++
  "# 1. Load Reference (Golden) Design\n" ++
  "read_sverilog -container r -libname WORK { " ++ goldFilesStr ++ " }\n" ++
  "set_top r:/WORK/" ++ goldName ++ "\n\n" ++
  "# 2. Load Implementation (Revised) Design\n" ++
  "read_sverilog -container i -libname WORK { " ++ revFilesStr ++ " }\n" ++
  "set_top i:/WORK/" ++ revName ++ "\n\n" ++
  "# 3. Match Compare Points\n" ++
  "match\n\n" ++
  "# 4. Verify Equivalence\n" ++
  "if { [verify] } {\n" ++
  "  puts \"SHOUMEI_SEC_PASS: Formality equivalence check SUCCEEDED\"\n" ++
  "  exit 0\n" ++
  "} else {\n" ++
  "  puts \"SHOUMEI_SEC_FAIL: Formality equivalence check FAILED\"\n" ++
  "  report_failing_points\n" ++
  "  exit 1\n" ++
  "}\n"

/-- Generate Open-Source Yosys verification TCL script. -/
def generateYosysTcl (goldName revName : String) (files : List String) : String :=
  let readCommands := files.map (fun f => "read_verilog -sv " ++ f)
  "# Yosys SEC / LEC Verification Script\n" ++
  "# Generated by Shoumei Codegen\n\n" ++
  String.intercalate "\n" readCommands ++ "\n\n" ++
  "# Build miter between reference and revised\n" ++
  "miter -equiv -flatten -make_outputs " ++ goldName ++ " " ++ revName ++ " miter_top\n" ++
  "hierarchy -top miter_top\n\n" ++
  "# SAT verification\n" ++
  "sat -verify -prove-asserts miter_top\n"

/-- Generate Synopsys VC Formal verification TCL script. -/
def generateVCFormalTcl (topName : String) (files : List String) (clkName : String := "clock") (rstName : String := "reset") (hasClock : Bool := true) : String :=
  let toBasename (f : String) : String := ((System.FilePath.mk f).fileName).getD f
  let filesStr := String.intercalate " " (files.map toBasename)
  let clkRstSection := if hasClock then
    "# Clock and reset constraints\n" ++
    "create_clock -period 10 " ++ clkName ++ "\n" ++
    "create_reset " ++ rstName ++ " -sense high\n\n"
  else
    "# Pure combinational module: no clock/reset constraints needed\n\n"
  "# Synopsys VC Formal Verification Script\n" ++
  "# Generated by Shoumei Codegen\n\n" ++
  "set_fml_appmode FPV\n\n" ++
  "# Read design files with SVA instrumentation\n" ++
  "read_file -format sverilog -vcs { +define+FORMAL " ++ filesStr ++ " }\n\n" ++
  "# Elaborate with SVA enabled\n" ++
  "elaborate -sva " ++ topName ++ "\n\n" ++
  clkRstSection ++
  "# Verify formal properties\n" ++
  "check_fv\n" ++
  "report_fv -list\n" ++
  "exit\n"

end Shoumei.Codegen.SECMiter
