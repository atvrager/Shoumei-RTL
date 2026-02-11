/-
Codegen/Testbench.lean - Testbench Code Generation

Generates SystemVerilog and SystemC testbenches from a TestbenchConfig.
The config maps circuit ports to memory interfaces (imem/dmem), control
signals, and constants. Generators produce:

- SV testbench: module instantiation, memory model, HTIF, DPI-C loader
- SystemC testbench: sc_main with bus pack/unpack helpers, memory model

Both share the same ELF loader library (testbench/lib/elf_loader.h).
-/

import Shoumei.DSL
import Shoumei.Codegen.Common
import Shoumei.Codegen.SystemVerilog

namespace Shoumei.Codegen.Testbench

open Shoumei
open Shoumei.Codegen

/-- A memory port describes how a CPU connects to a memory interface. -/
structure MemoryPort where
  addrSignal : String
  dataInSignal : Option String := none
  dataOutSignal : Option String := none
  validSignal : Option String := none
  readySignal : Option String := none
  weSignal : Option String := none
  respValidSignal : Option String := none
  respDataSignal : Option String := none
  deriving Repr

/-- Configuration for testbench generation. -/
structure TestbenchConfig where
  circuit : Circuit
  imemPort : MemoryPort
  dmemPort : MemoryPort
  memSizeWords : Nat := 16384
  tohostAddr : Nat := 0x1000
  timeoutCycles : Nat := 100000
  constantPorts : List (String × Bool) := [("zero", false), ("one", true)]
  /-- Override the testbench module/file name (default: tb_<circuit.name>) -/
  tbName : Option String := none
  debugOutputs : List String := []
  deriving Repr

/-! ## Helpers -/

private def optOrDefault (o : Option String) (d : String) : String :=
  match o with | some s => s | none => d

private def natToHexDigits (n : Nat) : String :=
  if n == 0 then "0"
  else String.ofList (Nat.toDigits 16 n)

private def hexLit (_width : Nat) (value : Nat) : String :=
  "32'h" ++ natToHexDigits value

/-! ## SystemVerilog Testbench Generator -/

def toTestbenchSV (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let inputGroups := SystemVerilog.autoDetectSignalGroups c.inputs
  let outputGroups := SystemVerilog.autoDetectSignalGroups c.outputs

  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)

  -- Build signal lists: (name, width) for inputs and outputs
  let inputBusWireNames := inputGroups.flatMap (fun sg => sg.wires.map Wire.name)
  let outputBusWireNames := outputGroups.flatMap (fun sg => sg.wires.map Wire.name)

  let inputSignals : List (String × Nat) :=
    let scalars := c.inputs.filter (fun w => !inputBusWireNames.contains w.name)
    scalars.map (fun w => (w.name, 1)) ++ inputGroups.map (fun sg => (sg.name, sg.width))

  let outputSignals : List (String × Nat) :=
    let scalars := c.outputs.filter (fun w => !outputBusWireNames.contains w.name)
    scalars.map (fun w => (w.name, 1)) ++ outputGroups.map (fun sg => (sg.name, sg.width))

  -- Filter: signals that are not clock/reset/constants
  let isSpecial (name : String) : Bool :=
    name == clockName || name == resetName ||
    cfg.constantPorts.any (fun (cn, _) => cn == name)

  -- Signal declarations
  let mkDecl (name : String) (width : Nat) : String :=
    if width > 1 then s!"  logic [{width-1}:0] {name};"
    else s!"  logic        {name};"

  let signalDecls := String.intercalate "\n" (
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w) ++
    (outputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w)
  )

  -- Port connections for CPU instance
  let portConns := String.intercalate ",\n" (
    [s!"      .{clockName}(clk)"] ++
    [s!"      .{resetName}({resetName})"] ++
    cfg.constantPorts.map (fun (name, value) =>
      s!"      .{name}(1'b{if value then "1" else "0"})") ++
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, _) =>
      s!"      .{n}({n})") ++
    outputSignals.map (fun (n, _) => s!"      .{n}({n})")
  )

  let pcSig := cfg.imemPort.addrSignal
  let imemDataIn := optOrDefault cfg.imemPort.dataInSignal "imem_resp_data"
  let dmemAddr := cfg.dmemPort.addrSignal
  let dmemValid := optOrDefault cfg.dmemPort.validSignal "dmem_req_valid"
  let dmemWe := optOrDefault cfg.dmemPort.weSignal "dmem_req_we"
  let dmemDataOut := optOrDefault cfg.dmemPort.dataOutSignal "dmem_req_data"
  let dmemReady := optOrDefault cfg.dmemPort.readySignal "dmem_req_ready"
  let dmemRespValid := optOrDefault cfg.dmemPort.respValidSignal "dmem_resp_valid"
  let dmemRespData := optOrDefault cfg.dmemPort.respDataSignal "dmem_resp_data"

  let memSizeStr := toString cfg.memSizeWords
  let timeoutStr := toString cfg.timeoutCycles
  let tohostHex := hexLit 32 cfg.tohostAddr

  let tbName := optOrDefault cfg.tbName s!"tb_{c.name}"

  -- Build the complete SV string
  "//==============================================================================\n" ++
  s!"// {tbName}.sv - Auto-generated testbench for {c.name}\n" ++
  "//\n" ++
  "// Generated by Shoumei RTL testbench code generator.\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++

  s!"module {tbName} #(\n" ++
  s!"    parameter MEM_SIZE_WORDS = {memSizeStr},\n" ++
  s!"    parameter TIMEOUT_CYCLES = {timeoutStr},\n" ++
  s!"    parameter TOHOST_ADDR    = {tohostHex}\n" ++
  ") (\n" ++
  "    input logic clk,\n" ++
  "    input logic rst_n,\n" ++
  "    // Test status\n" ++
  "    output logic        o_test_done,\n" ++
  "    output logic        o_test_pass,\n" ++
  "    output logic [31:0] o_test_code,\n" ++
  "    // Debug outputs\n" ++
  "    output logic [31:0] o_fetch_pc,\n" ++
  "    output logic        o_rob_empty,\n" ++
  "    output logic        o_global_stall,\n" ++
  "    output logic [31:0] o_cycle_count,\n" ++
  "    // Memory request observation\n" ++
  "    output logic        o_dmem_req_valid,\n" ++
  "    output logic        o_dmem_req_we,\n" ++
  "    output logic [31:0] o_dmem_req_addr,\n" ++
  "    output logic [31:0] o_dmem_req_data,\n" ++
  "    // HTIF\n" ++
  "    output logic [31:0] o_tohost,\n" ++
  "    // RVVI-TRACE outputs (cosimulation)\n" ++
  "    output logic        o_rvvi_valid,\n" ++
  "    output logic        o_rvvi_trap,\n" ++
  "    output logic [31:0] o_rvvi_pc_rdata,\n" ++
  "    output logic [31:0] o_rvvi_insn,\n" ++
  "    output logic [4:0]  o_rvvi_rd,\n" ++
  "    output logic        o_rvvi_rd_valid,\n" ++
  "    output logic [31:0] o_rvvi_rd_data,\n" ++
  "    // RVVI-TRACE FP outputs (F extension cosimulation)\n" ++
  "    output logic [4:0]  o_rvvi_frd,\n" ++
  "    output logic        o_rvvi_frd_valid,\n" ++
  "    output logic [31:0] o_rvvi_frd_data,\n" ++
  "    // FP exception flags accumulator\n" ++
  "    output logic [4:0]  o_fflags_acc\n" ++
  ");\n\n" ++
  "  // =========================================================================\n" ++
  "  // CPU I/O signals\n" ++
  "  // =========================================================================\n" ++
  signalDecls ++ "\n\n" ++
  s!"  logic        {resetName};\n" ++
  s!"  assign {resetName} = ~rst_n;\n\n" ++

  "  // =========================================================================\n" ++
  "  // CPU instance\n" ++
  "  // =========================================================================\n" ++
  s!"  {c.name} u_cpu (\n" ++
  portConns ++ "\n" ++
  "  );\n\n" ++

  "  // =========================================================================\n" ++
  "  // Memory: shared instruction + data, word-addressed\n" ++
  "  // =========================================================================\n" ++
  "  logic [31:0] mem [0:MEM_SIZE_WORDS-1];\n\n" ++
  "  // DPI-C: allow C++ to write memory words before simulation starts\n" ++
  "  export \"DPI-C\" function dpi_mem_write;\n" ++
  "  function void dpi_mem_write(input int unsigned word_addr, input int unsigned data);\n" ++
  "    mem[word_addr] = data;\n" ++
  "  endfunction\n\n" ++
  "  localparam logic [31:0] MEM_BASE = 32'h00000000;\n\n" ++
  "  function automatic logic [31:0] addr_to_idx(input logic [31:0] addr);\n" ++
  "    return (addr - MEM_BASE) >> 2;\n" ++
  "  endfunction\n\n" ++

  "  // --- Instruction memory: combinational read ---\n" ++
  s!"  assign {imemDataIn} = mem[addr_to_idx({pcSig})];\n\n" ++

  "  // --- Data memory: 1-cycle latency ---\n" ++
  "  logic        dmem_pending;\n" ++
  "  logic [31:0] dmem_read_data;\n\n" ++
  s!"  assign {dmemReady} = 1'b1;  // Always ready\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  s!"      {dmemRespValid} <= 1'b0;\n" ++
  "      dmem_read_data  <= 32'b0;\n" ++
  "      dmem_pending    <= 1'b0;\n" ++
  "    end else begin\n" ++
  "      dmem_pending    <= 1'b0;\n" ++
  s!"      {dmemRespValid} <= 1'b0;\n\n" ++
  s!"      if ({dmemValid}) begin\n" ++
  s!"        if ({dmemWe}) begin\n" ++
  "          // Store\n" ++
  s!"          mem[addr_to_idx({dmemAddr})] <= {dmemDataOut};\n" ++
  "        end else begin\n" ++
  "          // Load: respond next cycle\n" ++
  s!"          dmem_read_data  <= mem[addr_to_idx({dmemAddr})];\n" ++
  "          dmem_pending    <= 1'b1;\n" ++
  "        end\n" ++
  "      end\n\n" ++
  "      if (dmem_pending) begin\n" ++
  s!"        {dmemRespValid} <= 1'b1;\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++
  s!"  assign {dmemRespData} = dmem_read_data;\n\n" ++

  "  // =========================================================================\n" ++
  "  // HTIF: tohost termination\n" ++
  "  // =========================================================================\n" ++
  "  // Speculative stores are blocked by SB commit gating, so the first tohost\n" ++
  "  // write is always the correct committed one.\n" ++
  "  logic        test_done;\n" ++
  "  logic        test_pass;\n" ++
  "  logic [31:0] test_code;\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      test_done <= 1'b0;\n" ++
  "      test_pass <= 1'b0;\n" ++
  "      test_code <= 32'b0;\n" ++
  "    end else begin\n" ++
  s!"      if ({dmemValid} && {dmemWe} &&\n" ++
  s!"          {dmemAddr} == TOHOST_ADDR) begin\n" ++
  s!"        test_code <= {dmemDataOut};\n" ++
  s!"        test_pass <= ({dmemDataOut} == 32'h1);\n" ++
  "        test_done <= 1'b1;\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++

  "  // =========================================================================\n" ++
  "  // Cycle counter\n" ++
  "  // =========================================================================\n" ++
  "  logic [31:0] cycle_count;\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      cycle_count <= 32'b0;\n" ++
  "    end else begin\n" ++
  "      cycle_count <= cycle_count + 1;\n" ++
  "    end\n" ++
  "  end\n\n" ++

  "  // =========================================================================\n" ++
  "  // Debug trace (enable with +define+TRACE_PIPELINE)\n" ++
  "  // =========================================================================\n" ++
  "  `ifdef TRACE_PIPELINE\n" ++
  "  always_ff @(posedge clk) begin\n" ++
  s!"    if (!{resetName}) begin\n" ++
  "      $display(\"[%0d] PC=0x%08x stall=%b rob_empty=%b\",\n" ++
  s!"               cycle_count, {pcSig}, global_stall_out, rob_empty);\n" ++
  "    end\n" ++
  "  end\n" ++
  "  `endif\n\n" ++

  "  // =========================================================================\n" ++
  "  // Output assignments\n" ++
  "  // =========================================================================\n" ++
  "  assign o_test_done       = test_done;\n" ++
  "  assign o_test_pass       = test_pass;\n" ++
  "  assign o_test_code       = test_code;\n" ++
  s!"  assign o_fetch_pc       = {pcSig};\n" ++
  "  assign o_rob_empty       = rob_empty;\n" ++
  "  assign o_global_stall    = global_stall_out;\n" ++
  "  assign o_cycle_count     = cycle_count;\n" ++
  s!"  assign o_dmem_req_valid = {dmemValid};\n" ++
  s!"  assign o_dmem_req_we    = {dmemWe};\n" ++
  s!"  assign o_dmem_req_addr  = {dmemAddr};\n" ++
  s!"  assign o_dmem_req_data  = {dmemDataOut};\n" ++
  "  assign o_tohost          = test_code;\n" ++
  "  assign o_rvvi_valid      = rvvi_valid;\n" ++
  "  assign o_rvvi_trap       = rvvi_trap;\n" ++
  "  assign o_rvvi_pc_rdata   = rvvi_pc_rdata;\n" ++
  "  assign o_rvvi_insn       = rvvi_insn;\n" ++
  "  assign o_rvvi_rd         = rvvi_rd;\n" ++
  "  assign o_rvvi_rd_valid   = rvvi_rd_valid;\n" ++
  "  assign o_rvvi_rd_data    = rvvi_rd_data;\n" ++
  "  assign o_rvvi_frd        = rvvi_frd;\n" ++
  "  assign o_rvvi_frd_valid  = rvvi_frd_valid;\n" ++
  "  assign o_rvvi_frd_data   = rvvi_frd_data;\n" ++
  "  assign o_fflags_acc      = fflags_acc;\n\n" ++
  "endmodule\n"

/-! ## SystemC Testbench Generator -/

/-- Generate bus pack/unpack helpers for SystemC.
    These operate on sc_signal arrays (declared later in sc_main scope),
    not on module ports, because sc_in ports are read-only. -/
private def generateSystemCBusHelpers (c : Circuit) : String :=
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)
  let lb := "{"
  let rb := "}"
  let helpers := groups.map fun sg =>
    let width := sg.width
    let isInput := sg.wires.any (fun w => c.inputs.any (fun iw => iw.name == w.name))
    let isOutput := sg.wires.any (fun w => c.outputs.any (fun ow => ow.name == w.name))

    -- For input buses: write to the connected sc_signal (passed as array)
    let setter := if isInput then
      let lines := (List.range width).map fun i =>
        s!"    sigs[{i}]->write((v >> {i}) & 1);"
      "void set_" ++ sg.name ++ "(sc_signal<bool>* sigs[], uint32_t v) " ++ lb ++ "\n" ++
        String.intercalate "\n" lines ++ "\n" ++ rb
    else ""

    -- For output buses: read from the connected sc_signal
    let getter := if isOutput then
      let terms := (List.range width).map fun i =>
        if i == 0 then s!"(uint32_t)sigs[{i}]->read()"
        else s!"((uint32_t)sigs[{i}]->read() << {i})"
      "uint32_t get_" ++ sg.name ++ "(sc_signal<bool>* sigs[]) " ++ lb ++ "\n" ++
        "    return " ++ String.intercalate " | " terms ++ ";\n" ++ rb
    else ""

    let s1 := if setter.isEmpty then "" else setter ++ "\n\n"
    let s2 := if getter.isEmpty then "" else getter ++ "\n"
    s1 ++ s2
  String.intercalate "\n" (helpers.filter (· != ""))

/-- Generate a SystemC testbench (sc_main). -/
def toTestbenchSystemC (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)

  let busHelpers := generateSystemCBusHelpers c

  let inputGroups := SystemVerilog.autoDetectSignalGroups c.inputs
  let outputGroups := SystemVerilog.autoDetectSignalGroups c.outputs
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)

  let busWireNames : List String :=
    inputGroups.flatMap (fun sg => sg.wires.map Wire.name) ++
    outputGroups.flatMap (fun sg => sg.wires.map Wire.name)
  let scalarInputs := c.inputs.filter fun w =>
    !busWireNames.contains w.name &&
    w.name != clockName && w.name != resetName &&
    !cfg.constantPorts.any (fun (cn, _) => cn == w.name)
  let scalarOutputs := c.outputs.filter fun w =>
    !busWireNames.contains w.name

  let pcSig := cfg.imemPort.addrSignal
  let imemDataIn := optOrDefault cfg.imemPort.dataInSignal "imem_resp_data"
  let dmemAddr := cfg.dmemPort.addrSignal
  let dmemValid := optOrDefault cfg.dmemPort.validSignal "dmem_req_valid"
  let dmemWe := optOrDefault cfg.dmemPort.weSignal "dmem_req_we"
  let dmemDataOut := optOrDefault cfg.dmemPort.dataOutSignal "dmem_req_data"
  let dmemReady := optOrDefault cfg.dmemPort.readySignal "dmem_req_ready"
  let dmemRespValid := optOrDefault cfg.dmemPort.respValidSignal "dmem_resp_valid"
  let dmemRespData := optOrDefault cfg.dmemPort.respDataSignal "dmem_resp_data"

  let signalDecls := String.intercalate "\n" (
    scalarInputs.map (fun w => s!"    sc_signal<bool> {w.name}_sig;") ++
    scalarOutputs.map (fun w => s!"    sc_signal<bool> {w.name}_sig;") ++
    -- Constant port signals
    cfg.constantPorts.map (fun (name, _) => s!"    sc_signal<bool> {name}_sig;") ++
    -- Bus signal declarations
    groups.flatMap (fun sg =>
      (List.range sg.width).map fun i => s!"    sc_signal<bool> {sg.name}_{i}_sig;")
  )

  -- Signal array declarations for bus helpers
  let lb := "{"
  let rb := "}"
  let signalArrayDecls := String.intercalate "\n" (
    groups.map fun sg =>
      let ptrs := String.intercalate ", " (
        (List.range sg.width).map fun i => s!"&{sg.name}_{i}_sig")
      s!"    sc_signal<bool>* {sg.name}_sigs[] = {lb}{ptrs}{rb};"
  )

  let portBindings := String.intercalate "\n" (
    scalarInputs.map (fun w => s!"    u_cpu->{w.name}({w.name}_sig);") ++
    scalarOutputs.map (fun w => s!"    u_cpu->{w.name}({w.name}_sig);") ++
    -- Constant port bindings
    cfg.constantPorts.map (fun (name, _) => s!"    u_cpu->{name}({name}_sig);") ++
    groups.flatMap (fun sg =>
      (List.range sg.width).map fun i => s!"    u_cpu->{sg.name}_{i}({sg.name}_{i}_sig);")
  )

  let constBindings := String.intercalate "\n" (
    cfg.constantPorts.map fun (name, value) =>
      s!"    {name}_sig.write({if value then "true" else "false"});"
  )

  let lb := "{"
  let rb := "}"

  -- Generate ImemModel SC_MODULE port declarations
  let imemWidth := 32
  let pcWidth := 32
  let imemPortDecls := String.intercalate "\n" (
    (List.range pcWidth).map (fun i => s!"    sc_in<bool> {pcSig}_{i};") ++
    (List.range imemWidth).map (fun i => s!"    sc_out<bool> {imemDataIn}_{i};")
  )
  let imemSensitivity := String.intercalate " << " (
    (List.range pcWidth).map (fun i => s!"{pcSig}_{i}")
  )
  let imemGetPC := String.intercalate " | " (
    (List.range pcWidth).map fun i =>
      if i == 0 then s!"(uint32_t){pcSig}_{i}.read()"
      else s!"((uint32_t){pcSig}_{i}.read() << {i})"
  )
  let imemSetData := String.intercalate "\n" (
    (List.range imemWidth).map fun i =>
      s!"        {imemDataIn}_{i}.write((data >> {i}) & 1);"
  )

  -- ImemModel port bindings in sc_main
  let imemModelBindings := String.intercalate "\n" (
    (List.range pcWidth).map (fun i =>
      s!"    u_imem->{pcSig}_{i}({pcSig}_{i}_sig);") ++
    (List.range imemWidth).map (fun i =>
      s!"    u_imem->{imemDataIn}_{i}({imemDataIn}_{i}_sig);")
  )

  "//==============================================================================\n" ++
  s!"// sc_main_{c.name}.cpp - Auto-generated SystemC testbench\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++
  "#include <systemc.h>\n" ++
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstring>\n" ++
  s!"#include \"{c.name}.h\"\n" ++
  "#include \"elf_loader.h\"\n\n" ++
  s!"static const uint32_t MEM_SIZE_WORDS = {cfg.memSizeWords};\n" ++
  s!"static const uint32_t TOHOST_ADDR = 0x{natToHexDigits cfg.tohostAddr};\n" ++
  s!"static const uint32_t TIMEOUT_CYCLES = {cfg.timeoutCycles};\n\n" ++

  "// Memory model (shared between ImemModel and DmemModel)\n" ++
  s!"static uint32_t mem[{cfg.memSizeWords}];\n\n" ++
  s!"static void mem_write_cb(uint32_t addr, uint32_t data) {lb}\n" ++
  s!"    uint32_t widx = addr / 4;\n" ++
  s!"    if (widx < MEM_SIZE_WORDS) mem[widx] = data;\n" ++
  s!"{rb}\n\n" ++

  "// Bus pack/unpack helpers\n" ++
  busHelpers ++ "\n\n" ++

  "//------------------------------------------------------------------------------\n" ++
  "// ImemModel: Combinational instruction memory\n" ++
  "// Equivalent to SV: assign imem_resp_data = mem[fetch_pc >> 2];\n" ++
  "// SC_METHOD sensitive to fetch_pc bits ensures delta-cycle feedback works.\n" ++
  "//------------------------------------------------------------------------------\n" ++
  s!"SC_MODULE(ImemModel) {lb}\n" ++
  imemPortDecls ++ "\n\n" ++
  s!"    void update() {lb}\n" ++
  s!"        uint32_t pc = {imemGetPC};\n" ++
  s!"        uint32_t widx = pc >> 2;\n" ++
  s!"        uint32_t data = (widx < MEM_SIZE_WORDS) ? mem[widx] : 0;\n" ++
  imemSetData ++ "\n" ++
  s!"    {rb}\n\n" ++
  s!"    SC_CTOR(ImemModel) {lb}\n" ++
  s!"        SC_METHOD(update);\n" ++
  s!"        sensitive << {imemSensitivity};\n" ++
  s!"    {rb}\n" ++
  s!"{rb};\n\n" ++

  "//------------------------------------------------------------------------------\n" ++
  "// DmemModel: Data memory with 1-cycle read latency (manually clocked)\n" ++
  "// NOT an SC_MODULE - called explicitly from the simulation loop to avoid\n" ++
  "// timing issues with SC_CTHREAD firing before CPU eval.\n" ++
  "//------------------------------------------------------------------------------\n" ++
  s!"struct DmemModel {lb}\n" ++
  s!"    sc_signal<bool>& {dmemValid}_sig;\n" ++
  s!"    sc_signal<bool>& {dmemWe}_sig;\n" ++
  s!"    sc_signal<bool>& {dmemReady}_sig;\n" ++
  s!"    sc_signal<bool>& {dmemRespValid}_sig;\n" ++
  s!"    sc_signal<bool>** {dmemAddr}_sigs;\n" ++
  s!"    sc_signal<bool>** {dmemDataOut}_sigs;\n" ++
  s!"    sc_signal<bool>** {dmemRespData}_sigs;\n\n" ++
  s!"    bool pending;\n" ++
  s!"    uint32_t read_data;\n" ++
  s!"    bool test_done;\n" ++
  s!"    uint32_t test_data;\n\n" ++
  s!"    DmemModel(sc_signal<bool>& valid, sc_signal<bool>& we,\n" ++
  s!"             sc_signal<bool>& ready, sc_signal<bool>& resp_valid,\n" ++
  s!"             sc_signal<bool>** addr_sigs, sc_signal<bool>** data_out_sigs,\n" ++
  s!"             sc_signal<bool>** resp_data_sigs)\n" ++
  s!"        : {dmemValid}_sig(valid), {dmemWe}_sig(we),\n" ++
  s!"          {dmemReady}_sig(ready), {dmemRespValid}_sig(resp_valid),\n" ++
  s!"          {dmemAddr}_sigs(addr_sigs), {dmemDataOut}_sigs(data_out_sigs),\n" ++
  s!"          {dmemRespData}_sigs(resp_data_sigs),\n" ++
  s!"          pending(false), read_data(0), test_done(false), test_data(0)\n" ++
  s!"    {lb} {dmemReady}_sig.write(true); {rb}\n\n" ++
  s!"    void tick() {lb}\n" ++
  s!"        // Respond to pending load from previous cycle\n" ++
  s!"        if (pending) {lb}\n" ++
  s!"            {dmemRespValid}_sig.write(true);\n" ++
  s!"            for (int i = 0; i < 32; i++) {dmemRespData}_sigs[i]->write((read_data >> i) & 1);\n" ++
  s!"            pending = false;\n" ++
  s!"        {rb} else {lb}\n" ++
  s!"            {dmemRespValid}_sig.write(false);\n" ++
  s!"            for (int i = 0; i < 32; i++) {dmemRespData}_sigs[i]->write(false);\n" ++
  s!"        {rb}\n\n" ++
  s!"        // Handle new request\n" ++
  s!"        if ({dmemValid}_sig.read()) {lb}\n" ++
  s!"            uint32_t addr = get_{dmemAddr}({dmemAddr}_sigs);\n" ++
  s!"            if ({dmemWe}_sig.read()) {lb}\n" ++
  s!"                uint32_t data = get_{dmemDataOut}({dmemDataOut}_sigs);\n" ++
  s!"                if (addr == TOHOST_ADDR) {lb}\n" ++
  s!"                    test_done = true;\n" ++
  s!"                    test_data = data;\n" ++
  s!"                {rb} else {lb}\n" ++
  s!"                    uint32_t widx = addr >> 2;\n" ++
  s!"                    if (widx < MEM_SIZE_WORDS) mem[widx] = data;\n" ++
  s!"                {rb}\n" ++
  s!"            {rb} else {lb}\n" ++
  s!"                read_data = mem[addr >> 2];\n" ++
  s!"                pending = true;\n" ++
  s!"            {rb}\n" ++
  s!"        {rb}\n" ++
  s!"    {rb}\n" ++
  s!"{rb};\n\n" ++

  s!"int sc_main(int argc, char* argv[]) {lb}\n" ++
  "    // Suppress W571 (no activity for sc_start) — expected with manual eval\n" ++
  "    sc_report_handler::set_actions(SC_ID_NO_SC_START_ACTIVITY_, SC_DO_NOTHING);\n\n" ++
  "    const char* elf_path = nullptr;\n" ++
  s!"    uint32_t timeout = TIMEOUT_CYCLES;\n" ++
  s!"    for (int i = 1; i < argc; i++) {lb}\n" ++
  "        if (strncmp(argv[i], \"+elf=\", 5) == 0) elf_path = argv[i] + 5;\n" ++
  "        if (strncmp(argv[i], \"+timeout=\", 9) == 0) timeout = atoi(argv[i] + 9);\n" ++
  s!"    {rb}\n\n" ++
  s!"    if (!elf_path) {lb}\n" ++
  "        fprintf(stderr, \"ERROR: No ELF file. Use +elf=path\\n\");\n" ++
  "        return 1;\n" ++
  s!"    {rb}\n\n" ++
  "    memset(mem, 0, sizeof(mem));\n" ++
  "    if (load_elf(elf_path, mem_write_cb) < 0) return 1;\n\n" ++

  "    // Create signals\n" ++
  "    sc_clock clk(\"clk\", 10, SC_NS);\n" ++
  s!"    sc_signal<bool> {resetName}_sig;\n" ++
  signalDecls ++ "\n\n" ++

  "    // Signal arrays for bus helpers\n" ++
  signalArrayDecls ++ "\n\n" ++

  "    // Instantiate CPU (heap-allocated to avoid stack overflow)\n" ++
  s!"    auto* u_cpu = new {c.name}(\"u_cpu\");\n" ++
  s!"    u_cpu->{clockName}(clk);\n" ++
  s!"    u_cpu->{resetName}({resetName}_sig);\n" ++
  portBindings ++ "\n\n" ++

  "    // Instantiate combinational imem model\n" ++
  "    auto* u_imem = new ImemModel(\"u_imem\");\n" ++
  imemModelBindings ++ "\n\n" ++

  "    // Instantiate dmem model (manually clocked, not SC_MODULE)\n" ++
  s!"    auto* u_dmem = new DmemModel({dmemValid}_sig, {dmemWe}_sig,\n" ++
  s!"        {dmemReady}_sig, {dmemRespValid}_sig,\n" ++
  s!"        {dmemAddr}_sigs, {dmemDataOut}_sigs, {dmemRespData}_sigs);\n\n" ++

  "    // Constants\n" ++
  constBindings ++ "\n\n" ++

  "    // Trigger SystemC elaboration (binds all ports)\n" ++
  "    sc_start(SC_ZERO_TIME);\n\n" ++
  "    // Reset: hold reset high for 5 cycles\n" ++
  s!"    {resetName}_sig.write(true);\n" ++
  "    for (int r = 0; r < 5; r++) {\n" ++
  "        u_cpu->eval_seq_all();\n" ++
  "        for (int s = 0; s < 50; s++) { u_cpu->eval_comb_all(); sc_start(SC_ZERO_TIME); }\n" ++
  "    }\n" ++
  s!"    {resetName}_sig.write(false);\n\n" ++

  "    // Simulation loop: fully manual Verilator-style evaluation.\n" ++
  "    // No sc_clock needed — all timing is explicit.\n" ++
  "    bool done = false;\n" ++
  "    uint32_t cycle = 0;\n" ++
  "    printf(\"Simulation started (timeout=%u)\\n\", timeout);\n\n" ++

  s!"    while (!done && cycle < timeout) {lb}\n" ++
  "        // 1. DmemModel: respond to pending loads, handle new requests\n" ++
  "        u_dmem->tick();\n" ++
  "        sc_start(SC_ZERO_TIME);  // flush dmem writes\n\n" ++
  "        // 2. Latch all CPU DFFs (captures comb outputs from prev cycle)\n" ++
  "        u_cpu->eval_seq_all();\n" ++
  "        sc_start(SC_ZERO_TIME);  // flush DFF outputs\n\n" ++
  "        // 3. Settle combinational logic (multiple passes for hierarchy)\n" ++
  "        // Each pass: CPU comb -> flush -> ImemModel reacts -> flush\n" ++
  "        for (int settle = 0; settle < 50; settle++) {\n" ++
  "            u_cpu->eval_comb_all();\n" ++
  "            sc_start(SC_ZERO_TIME);\n" ++
  "        }\n" ++
  "        cycle++;\n\n" ++
  "        // Check tohost from DmemModel\n" ++
  s!"        if (u_dmem->test_done) {lb}\n" ++
  "            done = true;\n" ++
  "            printf(\"\\nTEST %s\\n\", u_dmem->test_data == 1 ? \"PASS\" : \"FAIL\");\n" ++
  "            printf(\"  Cycle: %u\\ntohost: 0x%08x\\n\", cycle, u_dmem->test_data);\n" ++
  s!"        {rb}\n\n" ++
  "        if (cycle % 10000 == 0)\n" ++
  s!"            printf(\"  [%u cycles] PC=0x%08x\\n\", cycle, get_{pcSig}({pcSig}_sigs));\n" ++
  s!"    {rb}\n\n" ++
  s!"    if (!done) {lb}\n" ++
  s!"        printf(\"TIMEOUT at cycle %u PC=0x%08x\\n\", cycle, get_{pcSig}({pcSig}_sigs));\n" ++
  s!"    {rb}\n" ++
  "    printf(\"Total cycles: %u\\n\", cycle);\n" ++
  "    delete u_dmem;\n" ++
  "    delete u_imem;\n" ++
  "    delete u_cpu;\n" ++
  "    // Note: sc_stop() not called; process exits directly.\n" ++
  "    return done ? 0 : 1;\n" ++
  s!"{rb}\n"

/-! ## CPU Setup File Generator (heavy compilation unit) -/

/-- Generate the thin header for CPU setup (no module includes needed). -/
private def toSetupHeader (c : Circuit) : String :=
  let lb := "{"
  let rb := "}"
  "// Auto-generated thin header for CPU setup. DO NOT EDIT.\n" ++
  s!"#ifndef SC_SETUP_{c.name.toUpper}_H\n" ++
  s!"#define SC_SETUP_{c.name.toUpper}_H\n\n" ++
  "#include <systemc.h>\n\n" ++
  s!"// Opaque handle to {c.name} instance + bound ports\n" ++
  s!"struct CpuCtx {lb}\n" ++
  "    void* cpu;\n" ++
  "    void eval_seq_all();\n" ++
  "    void eval_comb_all();\n" ++
  s!"{rb};\n\n" ++
  "// Create, bind ports (ports array order matches circuit definition), and return context\n" ++
  s!"CpuCtx* cpu_create(const char* name, sc_clock& clk, sc_signal<bool>& reset_sig,\n" ++
  "                    sc_signal<bool>* ports[], int num_ports);\n" ++
  "void cpu_delete(CpuCtx* ctx);\n\n" ++
  s!"#endif // SC_SETUP_{c.name.toUpper}_H\n"

/-- Generate the heavy setup .cpp file (includes the full module header). -/
private def toSetupCpp (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)
  let lb := "{"
  let rb := "}"

  -- Build port list (excluding clock/reset) in a canonical order
  let allPorts := c.inputs ++ c.outputs
  let portList := allPorts.filter fun w =>
    w.name != clockName && w.name != resetName
  let portBindings := String.intercalate "\n" (
    portList.enum.map fun ⟨idx, w⟩ =>
      s!"    cpu->{w.name}(*ports[{idx}]);"
  )

  s!"// Auto-generated CPU setup (heavy — includes full module headers). DO NOT EDIT.\n" ++
  s!"#include \"sc_setup_{c.name}.h\"\n" ++
  s!"#include \"{c.name}.h\"\n\n" ++
  s!"void CpuCtx::eval_seq_all() {lb} static_cast<{c.name}*>(cpu)->eval_seq_all(); {rb}\n" ++
  s!"void CpuCtx::eval_comb_all() {lb} static_cast<{c.name}*>(cpu)->eval_comb_all(); {rb}\n\n" ++
  s!"CpuCtx* cpu_create(const char* name, sc_clock& clk, sc_signal<bool>& reset_sig,\n" ++
  s!"                    sc_signal<bool>* ports[], int num_ports) {lb}\n" ++
  s!"    (void)num_ports;  // used for assert in debug builds\n" ++
  s!"    auto* cpu = new {c.name}(name);\n" ++
  s!"    cpu->{clockName}(clk);\n" ++
  s!"    cpu->{resetName}(reset_sig);\n" ++
  portBindings ++ "\n" ++
  s!"    auto* ctx = new CpuCtx{lb}cpu{rb};\n" ++
  "    return ctx;\n" ++
  s!"{rb}\n\n" ++
  s!"void cpu_delete(CpuCtx* ctx) {lb}\n" ++
  s!"    delete static_cast<{c.name}*>(ctx->cpu);\n" ++
  "    delete ctx;\n" ++
  s!"{rb}\n"

/-- Modify the SystemC sc_main to use the thin setup header instead of the heavy module header. -/
def toTestbenchSystemCThin (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)

  let busHelpers := generateSystemCBusHelpers c

  let inputGroups := SystemVerilog.autoDetectSignalGroups c.inputs
  let outputGroups := SystemVerilog.autoDetectSignalGroups c.outputs
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)

  let busWireNames : List String :=
    inputGroups.flatMap (fun sg => sg.wires.map Wire.name) ++
    outputGroups.flatMap (fun sg => sg.wires.map Wire.name)
  let scalarInputs := c.inputs.filter fun w =>
    !busWireNames.contains w.name &&
    w.name != clockName && w.name != resetName &&
    !cfg.constantPorts.any (fun (cn, _) => cn == w.name)
  let scalarOutputs := c.outputs.filter fun w =>
    !busWireNames.contains w.name

  let pcSig := cfg.imemPort.addrSignal
  let imemDataIn := optOrDefault cfg.imemPort.dataInSignal "imem_resp_data"
  let dmemAddr := cfg.dmemPort.addrSignal
  let dmemValid := optOrDefault cfg.dmemPort.validSignal "dmem_req_valid"
  let dmemWe := optOrDefault cfg.dmemPort.weSignal "dmem_req_we"
  let dmemDataOut := optOrDefault cfg.dmemPort.dataOutSignal "dmem_req_data"
  let dmemReady := optOrDefault cfg.dmemPort.readySignal "dmem_req_ready"
  let dmemRespValid := optOrDefault cfg.dmemPort.respValidSignal "dmem_resp_valid"
  let dmemRespData := optOrDefault cfg.dmemPort.respDataSignal "dmem_resp_data"

  let signalDecls := String.intercalate "\n" (
    scalarInputs.map (fun w => s!"    sc_signal<bool> {w.name}_sig;") ++
    scalarOutputs.map (fun w => s!"    sc_signal<bool> {w.name}_sig;") ++
    cfg.constantPorts.map (fun (name, _) => s!"    sc_signal<bool> {name}_sig;") ++
    groups.flatMap (fun sg =>
      (List.range sg.width).map fun i => s!"    sc_signal<bool> {sg.name}_{i}_sig;")
  )

  let lb := "{"
  let rb := "}"
  let signalArrayDecls := String.intercalate "\n" (
    groups.map fun sg =>
      let ptrs := String.intercalate ", " (
        (List.range sg.width).map fun i => s!"&{sg.name}_{i}_sig")
      s!"    sc_signal<bool>* {sg.name}_sigs[] = {lb}{ptrs}{rb};"
  )

  -- Build the port pointer array in the same order as toSetupCpp
  let allPorts := c.inputs ++ c.outputs
  let portList := allPorts.filter fun w =>
    w.name != clockName && w.name != resetName
  let portPtrArray := String.intercalate ", " (
    portList.map fun w => s!"&{w.name}_sig"
  )

  let constBindings := String.intercalate "\n" (
    cfg.constantPorts.map fun (name, value) =>
      s!"    {name}_sig.write({if value then "true" else "false"});"
  )

  -- ImemModel (same as before)
  let imemWidth := 32
  let pcWidth := 32
  let imemPortDecls := String.intercalate "\n" (
    (List.range pcWidth).map (fun i => s!"    sc_in<bool> {pcSig}_{i};") ++
    (List.range imemWidth).map (fun i => s!"    sc_out<bool> {imemDataIn}_{i};")
  )
  let imemSensitivity := String.intercalate " << " (
    (List.range pcWidth).map (fun i => s!"{pcSig}_{i}")
  )
  let imemGetPC := String.intercalate " | " (
    (List.range pcWidth).map fun i =>
      if i == 0 then s!"(uint32_t){pcSig}_{i}.read()"
      else s!"((uint32_t){pcSig}_{i}.read() << {i})"
  )
  let imemSetData := String.intercalate "\n" (
    (List.range imemWidth).map fun i =>
      s!"        {imemDataIn}_{i}.write((data >> {i}) & 1);"
  )
  let imemModelBindings := String.intercalate "\n" (
    (List.range pcWidth).map (fun i =>
      s!"    u_imem->{pcSig}_{i}({pcSig}_{i}_sig);") ++
    (List.range imemWidth).map (fun i =>
      s!"    u_imem->{imemDataIn}_{i}({imemDataIn}_{i}_sig);")
  )

  "//==============================================================================\n" ++
  s!"// sc_main_{c.name}.cpp - Auto-generated SystemC testbench (thin)\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++
  "#include <systemc.h>\n" ++
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstring>\n" ++
  s!"#include \"sc_setup_{c.name}.h\"\n" ++
  "#include \"elf_loader.h\"\n\n" ++
  s!"static const uint32_t MEM_SIZE_WORDS = {cfg.memSizeWords};\n" ++
  s!"static const uint32_t TOHOST_ADDR = 0x{natToHexDigits cfg.tohostAddr};\n" ++
  s!"static const uint32_t TIMEOUT_CYCLES = {cfg.timeoutCycles};\n\n" ++

  "// Memory model (shared between ImemModel and DmemModel)\n" ++
  s!"static uint32_t mem[{cfg.memSizeWords}];\n\n" ++
  s!"static void mem_write_cb(uint32_t addr, uint32_t data) {lb}\n" ++
  s!"    uint32_t widx = addr / 4;\n" ++
  s!"    if (widx < MEM_SIZE_WORDS) mem[widx] = data;\n" ++
  s!"{rb}\n\n" ++

  "// Bus pack/unpack helpers\n" ++
  busHelpers ++ "\n\n" ++

  "//------------------------------------------------------------------------------\n" ++
  "// ImemModel: Combinational instruction memory\n" ++
  "//------------------------------------------------------------------------------\n" ++
  s!"SC_MODULE(ImemModel) {lb}\n" ++
  imemPortDecls ++ "\n\n" ++
  s!"    void update() {lb}\n" ++
  s!"        uint32_t pc = {imemGetPC};\n" ++
  s!"        uint32_t widx = pc >> 2;\n" ++
  s!"        uint32_t data = (widx < MEM_SIZE_WORDS) ? mem[widx] : 0;\n" ++
  imemSetData ++ "\n" ++
  s!"    {rb}\n\n" ++
  s!"    SC_CTOR(ImemModel) {lb}\n" ++
  s!"        SC_METHOD(update);\n" ++
  s!"        sensitive << {imemSensitivity};\n" ++
  s!"    {rb}\n" ++
  s!"{rb};\n\n" ++

  "//------------------------------------------------------------------------------\n" ++
  "// DmemModel: Data memory with 1-cycle read latency (manually clocked)\n" ++
  "//------------------------------------------------------------------------------\n" ++
  s!"struct DmemModel {lb}\n" ++
  s!"    sc_signal<bool>& {dmemValid}_sig;\n" ++
  s!"    sc_signal<bool>& {dmemWe}_sig;\n" ++
  s!"    sc_signal<bool>& {dmemReady}_sig;\n" ++
  s!"    sc_signal<bool>& {dmemRespValid}_sig;\n" ++
  s!"    sc_signal<bool>** {dmemAddr}_sigs;\n" ++
  s!"    sc_signal<bool>** {dmemDataOut}_sigs;\n" ++
  s!"    sc_signal<bool>** {dmemRespData}_sigs;\n\n" ++
  s!"    bool pending;\n" ++
  s!"    uint32_t read_data;\n" ++
  s!"    bool test_done;\n" ++
  s!"    uint32_t test_data;\n\n" ++
  s!"    DmemModel(sc_signal<bool>& valid, sc_signal<bool>& we,\n" ++
  s!"             sc_signal<bool>& ready, sc_signal<bool>& resp_valid,\n" ++
  s!"             sc_signal<bool>** addr_sigs, sc_signal<bool>** data_out_sigs,\n" ++
  s!"             sc_signal<bool>** resp_data_sigs)\n" ++
  s!"        : {dmemValid}_sig(valid), {dmemWe}_sig(we),\n" ++
  s!"          {dmemReady}_sig(ready), {dmemRespValid}_sig(resp_valid),\n" ++
  s!"          {dmemAddr}_sigs(addr_sigs), {dmemDataOut}_sigs(data_out_sigs),\n" ++
  s!"          {dmemRespData}_sigs(resp_data_sigs),\n" ++
  s!"          pending(false), read_data(0), test_done(false), test_data(0)\n" ++
  s!"    {lb} {dmemReady}_sig.write(true); {rb}\n\n" ++
  s!"    void tick() {lb}\n" ++
  s!"        if (pending) {lb}\n" ++
  s!"            {dmemRespValid}_sig.write(true);\n" ++
  s!"            for (int i = 0; i < 32; i++) {dmemRespData}_sigs[i]->write((read_data >> i) & 1);\n" ++
  s!"            pending = false;\n" ++
  s!"        {rb} else {lb}\n" ++
  s!"            {dmemRespValid}_sig.write(false);\n" ++
  s!"            for (int i = 0; i < 32; i++) {dmemRespData}_sigs[i]->write(false);\n" ++
  s!"        {rb}\n\n" ++
  s!"        if ({dmemValid}_sig.read()) {lb}\n" ++
  s!"            uint32_t addr = get_{dmemAddr}({dmemAddr}_sigs);\n" ++
  s!"            if ({dmemWe}_sig.read()) {lb}\n" ++
  s!"                uint32_t data = get_{dmemDataOut}({dmemDataOut}_sigs);\n" ++
  s!"                if (addr == TOHOST_ADDR) {lb}\n" ++
  s!"                    test_done = true;\n" ++
  s!"                    test_data = data;\n" ++
  s!"                {rb} else {lb}\n" ++
  s!"                    uint32_t widx = addr >> 2;\n" ++
  s!"                    if (widx < MEM_SIZE_WORDS) mem[widx] = data;\n" ++
  s!"                {rb}\n" ++
  s!"            {rb} else {lb}\n" ++
  s!"                read_data = mem[addr >> 2];\n" ++
  s!"                pending = true;\n" ++
  s!"            {rb}\n" ++
  s!"        {rb}\n" ++
  s!"    {rb}\n" ++
  s!"{rb};\n\n" ++

  s!"int sc_main(int argc, char* argv[]) {lb}\n" ++
  "    sc_report_handler::set_actions(SC_ID_NO_SC_START_ACTIVITY_, SC_DO_NOTHING);\n\n" ++
  "    const char* elf_path = nullptr;\n" ++
  s!"    uint32_t timeout = TIMEOUT_CYCLES;\n" ++
  s!"    for (int i = 1; i < argc; i++) {lb}\n" ++
  "        if (strncmp(argv[i], \"+elf=\", 5) == 0) elf_path = argv[i] + 5;\n" ++
  "        if (strncmp(argv[i], \"+timeout=\", 9) == 0) timeout = atoi(argv[i] + 9);\n" ++
  s!"    {rb}\n\n" ++
  s!"    if (!elf_path) {lb}\n" ++
  "        fprintf(stderr, \"ERROR: No ELF file. Use +elf=path\\n\");\n" ++
  "        return 1;\n" ++
  s!"    {rb}\n\n" ++
  "    memset(mem, 0, sizeof(mem));\n" ++
  "    if (load_elf(elf_path, mem_write_cb) < 0) return 1;\n\n" ++

  "    // Create signals\n" ++
  "    sc_clock clk(\"clk\", 10, SC_NS);\n" ++
  s!"    sc_signal<bool> {resetName}_sig;\n" ++
  signalDecls ++ "\n\n" ++

  "    // Signal arrays for bus helpers\n" ++
  signalArrayDecls ++ "\n\n" ++

  "    // Port pointer array (order matches sc_setup port binding)\n" ++
  s!"    sc_signal<bool>* cpu_ports[] = {lb}{portPtrArray}{rb};\n\n" ++

  "    // Create and bind CPU via setup module\n" ++
  s!"    CpuCtx* u_cpu = cpu_create(\"u_cpu\", clk, {resetName}_sig,\n" ++
  s!"        cpu_ports, {portList.length});\n\n" ++

  "    // Instantiate combinational imem model\n" ++
  "    auto* u_imem = new ImemModel(\"u_imem\");\n" ++
  imemModelBindings ++ "\n\n" ++

  "    // Instantiate dmem model (manually clocked, not SC_MODULE)\n" ++
  s!"    auto* u_dmem = new DmemModel({dmemValid}_sig, {dmemWe}_sig,\n" ++
  s!"        {dmemReady}_sig, {dmemRespValid}_sig,\n" ++
  s!"        {dmemAddr}_sigs, {dmemDataOut}_sigs, {dmemRespData}_sigs);\n\n" ++

  "    // Constants\n" ++
  constBindings ++ "\n\n" ++

  "    // Trigger SystemC elaboration (binds all ports)\n" ++
  "    sc_start(SC_ZERO_TIME);\n\n" ++
  "    // Reset: hold reset high for 5 cycles\n" ++
  s!"    {resetName}_sig.write(true);\n" ++
  "    for (int r = 0; r < 5; r++) {\n" ++
  "        u_cpu->eval_seq_all();\n" ++
  "        for (int s = 0; s < 50; s++) { u_cpu->eval_comb_all(); sc_start(SC_ZERO_TIME); }\n" ++
  "    }\n" ++
  s!"    {resetName}_sig.write(false);\n\n" ++

  "    // Simulation loop\n" ++
  "    bool done = false;\n" ++
  "    uint32_t cycle = 0;\n" ++
  "    printf(\"Simulation started (timeout=%u)\\n\", timeout);\n\n" ++

  s!"    while (!done && cycle < timeout) {lb}\n" ++
  "        u_dmem->tick();\n" ++
  "        sc_start(SC_ZERO_TIME);\n\n" ++
  "        u_cpu->eval_seq_all();\n" ++
  "        sc_start(SC_ZERO_TIME);\n\n" ++
  "        for (int settle = 0; settle < 50; settle++) {\n" ++
  "            u_cpu->eval_comb_all();\n" ++
  "            sc_start(SC_ZERO_TIME);\n" ++
  "        }\n" ++
  "        cycle++;\n\n" ++
  s!"        if (u_dmem->test_done) {lb}\n" ++
  "            done = true;\n" ++
  "            printf(\"\\nTEST %s\\n\", u_dmem->test_data == 1 ? \"PASS\" : \"FAIL\");\n" ++
  "            printf(\"  Cycle: %u\\ntohost: 0x%08x\\n\", cycle, u_dmem->test_data);\n" ++
  s!"        {rb}\n\n" ++
  "        if (cycle % 10000 == 0)\n" ++
  s!"            printf(\"  [%u cycles] PC=0x%08x\\n\", cycle, get_{pcSig}({pcSig}_sigs));\n" ++
  s!"    {rb}\n\n" ++
  s!"    if (!done) {lb}\n" ++
  s!"        printf(\"TIMEOUT at cycle %u PC=0x%08x\\n\", cycle, get_{pcSig}({pcSig}_sigs));\n" ++
  s!"    {rb}\n" ++
  "    printf(\"Total cycles: %u\\n\", cycle);\n" ++
  "    delete u_dmem;\n" ++
  "    delete u_imem;\n" ++
  "    cpu_delete(u_cpu);\n" ++
  "    return done ? 0 : 1;\n" ++
  s!"{rb}\n"

/-! ## File Writers -/

def testbenchOutputDir : String := "testbench/generated"

def writeTestbenchSV (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let sv := toTestbenchSV cfg
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let path := s!"{testbenchOutputDir}/{tbName}.sv"
  IO.FS.writeFile path sv
  IO.println s!"  ✓ {tbName}.sv (testbench)"

def writeTestbenchSystemC (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let c := cfg.circuit
  -- Write thin setup header
  let setupH := toSetupHeader c
  IO.FS.writeFile s!"{testbenchOutputDir}/sc_setup_{c.name}.h" setupH
  -- Write heavy setup cpp (includes full module header)
  let setupCpp := toSetupCpp cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/sc_setup_{c.name}.cpp" setupCpp
  -- Write thin sc_main (no module header includes)
  let sc := toTestbenchSystemCThin cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/sc_main_{c.name}.cpp" sc
  IO.println s!"  ✓ sc_main_{c.name}.cpp + sc_setup_{c.name}.cpp (testbench, split)"

def writeTestbenches (cfg : TestbenchConfig) : IO Unit := do
  Testbench.writeTestbenchSV cfg
  Testbench.writeTestbenchSystemC cfg

end Shoumei.Codegen.Testbench
