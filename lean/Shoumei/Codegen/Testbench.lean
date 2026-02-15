/-
Codegen/Testbench.lean - Testbench Code Generation

Generates SystemVerilog and plain C++ simulation testbenches from a
TestbenchConfig. The config maps circuit ports to memory interfaces
(imem/dmem), control signals, and constants. Generators produce:

- SV testbench: module instantiation, memory model, HTIF, DPI-C loader
- C++ sim testbench: plain bool signals, manual eval loop, no SystemC

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
  /-- Store size signal (2-bit): 00=byte, 01=half, 10=word. When set, byte-enable
      store logic is generated. The signal may be a bus or individual bits
      (detected automatically from the circuit outputs). -/
  sizeSignal : Option String := none
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
  /-- MMIO putchar address. Writes to this address emit the low byte to $write. -/
  putcharAddr : Option Nat := none
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

  -- Size signal handling (must be before signalDecls/portConns)
  let dmemSize := cfg.dmemPort.sizeSignal
  -- Check RAW circuit outputs (before signal group reconstruction) for individual bits
  let sizeIsBitwise := match dmemSize with
    | some sizeName => c.outputs.any (fun w => w.name == s!"{sizeName}_0")
    | none => false

  -- When size signal uses individual bits, exclude the grouped bus from declarations
  -- and port connections (we'll add individual bit connections instead)
  let isSizeBus (name : String) : Bool := match dmemSize with
    | some sizeName => sizeIsBitwise && name == sizeName
    | none => false

  let signalDecls := String.intercalate "\n" (
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w) ++
    (outputSignals.filter (fun (n, _) => !isSpecial n && !isSizeBus n)).map (fun (n, w) => mkDecl n w)
  )

  -- Port connections for CPU instance
  let portConns := String.intercalate ",\n" (
    [s!"      .{clockName}(clk)"] ++
    [s!"      .{resetName}({resetName})"] ++
    cfg.constantPorts.map (fun (name, value) =>
      s!"      .{name}(1'b{if value then "1" else "0"})") ++
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, _) =>
      s!"      .{n}({n})") ++
    (outputSignals.filter (fun (n, _) => !isSizeBus n)).map (fun (n, _) =>
      s!"      .{n}({n})") ++
    -- Add individual bit connections for size signal
    (match dmemSize with
     | some sizeName => if sizeIsBitwise then
         [s!"      .{sizeName}_0({sizeName}_0)",
          s!"      .{sizeName}_1({sizeName}_1)"]
       else []
     | none => [])
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
  let putcharParam := match cfg.putcharAddr with
    | some addr => s!",\n    parameter PUTCHAR_ADDR    = {hexLit 32 addr}"
    | none => ""

  let tbName := optOrDefault cfg.tbName s!"tb_{c.name}"

  -- Size signal declarations (individual bits → combined wire, or just reference bus)
  let sizeDeclStr := match dmemSize with
    | some sizeName =>
      if sizeIsBitwise then
        s!"  logic       {sizeName}_0;\n" ++
        s!"  logic       {sizeName}_1;\n" ++
        "  wire  [1:0] " ++ sizeName ++ " = {" ++ sizeName ++ "_1, " ++ sizeName ++ "_0};\n"
      else ""
    | none => ""

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
  putcharParam ++
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
  signalDecls ++ "\n" ++
  sizeDeclStr ++ "\n" ++
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
  "  // DPI-C: allow C++ to override HTIF addresses from ELF symbols\n" ++
  "  logic [31:0] tohost_addr_r;\n" ++
  "  initial tohost_addr_r = TOHOST_ADDR;\n" ++
  "  export \"DPI-C\" function dpi_set_tohost_addr;\n" ++
  "  function void dpi_set_tohost_addr(input int unsigned addr);\n" ++
  "    tohost_addr_r = addr;\n" ++
  "  endfunction\n\n" ++
  (match cfg.putcharAddr with
   | some _ =>
     "  logic [31:0] putchar_addr_r;\n" ++
     "  initial putchar_addr_r = PUTCHAR_ADDR;\n" ++
     "  export \"DPI-C\" function dpi_set_putchar_addr;\n" ++
     "  function void dpi_set_putchar_addr(input int unsigned addr);\n" ++
     "    putchar_addr_r = addr;\n" ++
     "  endfunction\n\n"
   | none => "") ++
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
  (match dmemSize with
   | some sizeName =>
     s!"          // Store with byte-enable based on {sizeName} and addr[1:0]\n" ++
     s!"          // {sizeName}: 00=byte, 01=half, 10=word\n" ++
     s!"          case ({sizeName})\n" ++
     s!"            2'b00: begin // SB: store byte\n" ++
     s!"              case ({dmemAddr}[1:0])\n" ++
     s!"                2'b00: mem[addr_to_idx({dmemAddr})][7:0]   <= {dmemDataOut}[7:0];\n" ++
     s!"                2'b01: mem[addr_to_idx({dmemAddr})][15:8]  <= {dmemDataOut}[7:0];\n" ++
     s!"                2'b10: mem[addr_to_idx({dmemAddr})][23:16] <= {dmemDataOut}[7:0];\n" ++
     s!"                2'b11: mem[addr_to_idx({dmemAddr})][31:24] <= {dmemDataOut}[7:0];\n" ++
     s!"              endcase\n" ++
     s!"            end\n" ++
     s!"            2'b01: begin // SH: store halfword\n" ++
     s!"              case ({dmemAddr}[1])\n" ++
     s!"                1'b0: mem[addr_to_idx({dmemAddr})][15:0]  <= {dmemDataOut}[15:0];\n" ++
     s!"                1'b1: mem[addr_to_idx({dmemAddr})][31:16] <= {dmemDataOut}[15:0];\n" ++
     s!"              endcase\n" ++
     s!"            end\n" ++
     s!"            default: begin // SW: store word\n" ++
     s!"              mem[addr_to_idx({dmemAddr})] <= {dmemDataOut};\n" ++
     s!"            end\n" ++
     s!"          endcase\n"
   | none =>
     s!"          // Store\n" ++
     s!"          mem[addr_to_idx({dmemAddr})] <= {dmemDataOut};\n") ++
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
  s!"          {dmemAddr} == tohost_addr_r) begin\n" ++
  s!"        test_code <= {dmemDataOut};\n" ++
  s!"        test_pass <= ({dmemDataOut} == 32'h1);\n" ++
  "        test_done <= 1'b1;\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++

  -- MMIO putchar support
  (match cfg.putcharAddr with
   | some _ =>
     "  // =========================================================================\n" ++
     "  // MMIO putchar: writes to PUTCHAR_ADDR emit a character\n" ++
     "  // =========================================================================\n" ++
     s!"  always_ff @(posedge clk) begin\n" ++
     s!"    if (!{resetName} && {dmemValid} && {dmemWe} &&\n" ++
     s!"        {dmemAddr} == putchar_addr_r) begin\n" ++
     s!"      $write(\"%c\", {dmemDataOut}[7:0]);\n" ++
     "    end\n" ++
     "  end\n\n"
   | none => "") ++

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

/-! ## Plain C++ Simulation Testbench Generator -/

/-- Generate bus pack/unpack helpers for plain C++ simulation.
    These operate on bool* arrays (declared later in main scope). -/
private def generateCppSimBusHelpers (c : Circuit) : String :=
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)
  let lb := "{"
  let rb := "}"
  let helpers := groups.map fun sg =>
    let width := sg.width
    let isInput := sg.wires.any (fun w => c.inputs.any (fun iw => iw.name == w.name))
    let isOutput := sg.wires.any (fun w => c.outputs.any (fun ow => ow.name == w.name))

    -- For input buses: write to the connected bool (passed as pointer array)
    let setter := if isInput then
      let lines := (List.range width).map fun i =>
        s!"    *sigs[{i}] = (v >> {i}) & 1;"
      "void set_" ++ sg.name ++ "(bool** sigs, uint32_t v) " ++ lb ++ "\n" ++
        String.intercalate "\n" lines ++ "\n" ++ rb
    else ""

    -- For output buses: read from the connected bool
    let getter := if isOutput then
      let terms := (List.range width).map fun i =>
        if i == 0 then s!"(uint32_t)(*sigs[{i}])"
        else s!"((uint32_t)(*sigs[{i}]) << {i})"
      "uint32_t get_" ++ sg.name ++ "(bool** sigs) " ++ lb ++ "\n" ++
        "    return " ++ String.intercalate " | " terms ++ ";\n" ++ rb
    else ""

    let s1 := if setter.isEmpty then "" else setter ++ "\n\n"
    let s2 := if getter.isEmpty then "" else getter ++ "\n"
    s1 ++ s2
  String.intercalate "\n" (helpers.filter (· != ""))

/-! ## CPU Setup File Generator -/

/-- Generate the thin header for CPU setup (plain C++, no SystemC). -/
private def toCpuSetupHeader (c : Circuit) : String :=
  let lb := "{"
  let rb := "}"
  "// Auto-generated thin header for CPU setup. DO NOT EDIT.\n" ++
  s!"#ifndef CPU_SETUP_{c.name.toUpper}_H\n" ++
  s!"#define CPU_SETUP_{c.name.toUpper}_H\n\n" ++
  "#include <cstdint>\n\n" ++
  s!"// Opaque handle to {c.name} instance + bound ports\n" ++
  s!"struct CpuCtx {lb}\n" ++
  "    void* cpu;\n" ++
  s!"{rb};\n\n" ++
  "// Create, bind ports (ports array order matches circuit definition), and return context\n" ++
  s!"CpuCtx* cpu_create(const char* name, bool* reset_sig,\n" ++
  "                    bool* ports[], int num_ports);\n" ++
  "void cpu_delete(CpuCtx* ctx);\n" ++
  "// Manual evaluation\n" ++
  "void cpu_eval_comb_all(CpuCtx* ctx);\n" ++
  "void cpu_eval_seq_all(CpuCtx* ctx);\n\n" ++
  s!"#endif // CPU_SETUP_{c.name.toUpper}_H\n"

/-- Generate the heavy setup .cpp file (includes the full module header). -/
private def toCpuSetupCpp (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let _clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)
  let lb := "{"
  let rb := "}"

  -- Build port list (excluding reset only; clock is included as a dummy bool*)
  let allPorts := c.inputs ++ c.outputs
  let portList := allPorts.filter fun w =>
    w.name != resetName
  let portBindings := String.intercalate "\n" (
    portList.enum.map fun ⟨idx, w⟩ =>
      s!"    cpu->{w.name} = ports[{idx}];"
  )

  s!"// Auto-generated CPU setup (heavy -- includes full module headers). DO NOT EDIT.\n" ++
  s!"#include \"cpu_setup_{c.name}.h\"\n" ++
  s!"#include \"{c.name}.h\"\n\n" ++
  s!"CpuCtx* cpu_create(const char* name, bool* reset_sig,\n" ++
  s!"                    bool* ports[], int num_ports) {lb}\n" ++
  s!"    (void)name; (void)num_ports;  // used for assert in debug builds\n" ++
  s!"    auto* cpu = new {c.name}();\n" ++
  s!"    cpu->{resetName} = reset_sig;\n" ++
  portBindings ++ "\n" ++
  s!"    cpu->bind_ports();\n" ++
  s!"    auto* ctx = new CpuCtx{lb}cpu{rb};\n" ++
  "    return ctx;\n" ++
  s!"{rb}\n\n" ++
  s!"void cpu_delete(CpuCtx* ctx) {lb}\n" ++
  s!"    delete static_cast<{c.name}*>(ctx->cpu);\n" ++
  "    delete ctx;\n" ++
  s!"{rb}\n\n" ++
  s!"void cpu_eval_comb_all(CpuCtx* ctx) {lb}\n" ++
  s!"    static_cast<{c.name}*>(ctx->cpu)->eval_comb_all();\n" ++
  s!"{rb}\n\n" ++
  s!"void cpu_eval_seq_all(CpuCtx* ctx) {lb}\n" ++
  s!"    static_cast<{c.name}*>(ctx->cpu)->eval_seq_all();\n" ++
  s!"{rb}\n"

/-- Generate a plain C++ simulation testbench (no SystemC dependency). -/
def toTestbenchCppSim (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let _clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)

  let busHelpers := generateCppSimBusHelpers c

  let inputGroups := SystemVerilog.autoDetectSignalGroups c.inputs
  let outputGroups := SystemVerilog.autoDetectSignalGroups c.outputs
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)

  let busWireNames : List String :=
    inputGroups.flatMap (fun sg => sg.wires.map Wire.name) ++
    outputGroups.flatMap (fun sg => sg.wires.map Wire.name)
  let scalarInputs := c.inputs.filter fun w =>
    !busWireNames.contains w.name &&
    w.name != resetName &&
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
  let dmemSize := cfg.dmemPort.sizeSignal

  let signalDecls := String.intercalate "\n" (
    scalarInputs.map (fun w => s!"    bool {w.name}_sig = false;") ++
    scalarOutputs.map (fun w => s!"    bool {w.name}_sig = false;") ++
    cfg.constantPorts.map (fun (name, _) => s!"    bool {name}_sig = false;") ++
    groups.flatMap (fun sg =>
      (List.range sg.width).map fun i => s!"    bool {sg.name}_{i}_sig = false;")
  )

  let lb := "{"
  let rb := "}"
  let signalArrayDecls := String.intercalate "\n" (
    groups.map fun sg =>
      let ptrs := String.intercalate ", " (
        (List.range sg.width).map fun i => s!"&{sg.name}_{i}_sig")
      s!"    bool* {sg.name}_sigs[] = {lb}{ptrs}{rb};"
  )

  -- Build the port pointer array in the same order as toCpuSetupCpp
  let allPorts := c.inputs ++ c.outputs
  let portList := allPorts.filter fun w =>
    w.name != resetName
  let portPtrArray := String.intercalate ", " (
    portList.map fun w => s!"&{w.name}_sig"
  )

  let constBindings := String.intercalate "\n" (
    cfg.constantPorts.map fun (name, value) =>
      s!"    {name}_sig = {if value then "true" else "false"};"
  )

  "//==============================================================================\n" ++
  s!"// sim_main_{c.name}.cpp - Auto-generated plain C++ simulation testbench\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++
  "#include <cstdint>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstring>\n" ++
  "#include <cstdio>\n" ++
  s!"#include \"cpu_setup_{c.name}.h\"\n" ++
  "#include \"elf_loader.h\"\n\n" ++
  s!"static const uint32_t MEM_SIZE_WORDS = {cfg.memSizeWords};\n" ++
  s!"static const uint32_t TOHOST_ADDR = 0x{natToHexDigits cfg.tohostAddr};\n" ++
  (match cfg.putcharAddr with
   | some addr => s!"static const uint32_t PUTCHAR_ADDR = 0x{natToHexDigits addr};\n"
   | none => "") ++
  s!"static const uint32_t TIMEOUT_CYCLES = {cfg.timeoutCycles};\n\n" ++

  "// Memory model\n" ++
  s!"static uint32_t mem[{cfg.memSizeWords}];\n\n" ++
  s!"static void mem_write_cb(uint32_t addr, uint32_t data) {lb}\n" ++
  s!"    uint32_t widx = addr / 4;\n" ++
  s!"    if (widx < MEM_SIZE_WORDS) mem[widx] = data;\n" ++
  s!"{rb}\n\n" ++

  "// Bus pack/unpack helpers\n" ++
  busHelpers ++ "\n\n" ++

  "//------------------------------------------------------------------------------\n" ++
  "// Imem: combinational instruction memory (plain function)\n" ++
  "//------------------------------------------------------------------------------\n" ++
  s!"static void imem_update(bool** pc_sigs, bool** data_sigs) {lb}\n" ++
  s!"    uint32_t pc_val = 0;\n" ++
  s!"    for (int i = 0; i < 32; i++) pc_val |= (*pc_sigs[i] ? 1u : 0u) << i;\n" ++
  s!"    uint32_t widx = pc_val >> 2;\n" ++
  s!"    uint32_t dval = (widx < MEM_SIZE_WORDS) ? mem[widx] : 0;\n" ++
  s!"    for (int i = 0; i < 32; i++) *data_sigs[i] = (dval >> i) & 1;\n" ++
  s!"{rb}\n\n" ++

  "//------------------------------------------------------------------------------\n" ++
  "// Dmem: data memory with 1-cycle read latency, byte/halfword/word stores\n" ++
  "//------------------------------------------------------------------------------\n" ++
  s!"struct DmemState {lb}\n" ++
  s!"    bool pending = false;\n" ++
  s!"    uint32_t read_data = 0;\n" ++
  s!"    bool test_done = false;\n" ++
  s!"    uint32_t test_data = 0;\n" ++
  s!"{rb};\n\n" ++
  s!"static void dmem_tick(DmemState& ds,\n" ++
  s!"    bool& req_valid_sig, bool& req_we_sig,\n" ++
  s!"    bool& req_ready_sig, bool& resp_valid_sig,\n" ++
  s!"    bool** req_addr_sigs, bool** req_data_sigs,\n" ++
  s!"    bool** resp_data_sigs,\n" ++
  s!"    bool** req_size_sigs = nullptr) {lb}\n" ++
  s!"    req_ready_sig = true;\n\n" ++
  s!"    // Respond to pending load from previous cycle\n" ++
  s!"    if (ds.pending) {lb}\n" ++
  s!"        resp_valid_sig = true;\n" ++
  s!"        for (int i = 0; i < 32; i++) *resp_data_sigs[i] = (ds.read_data >> i) & 1;\n" ++
  s!"        ds.pending = false;\n" ++
  s!"    {rb} else {lb}\n" ++
  s!"        resp_valid_sig = false;\n" ++
  s!"        for (int i = 0; i < 32; i++) *resp_data_sigs[i] = false;\n" ++
  s!"    {rb}\n\n" ++
  s!"    // Handle new request\n" ++
  s!"    if (req_valid_sig) {lb}\n" ++
  s!"        uint32_t addr = 0;\n" ++
  s!"        for (int i = 0; i < 32; i++) addr |= (*req_addr_sigs[i] ? 1u : 0u) << i;\n" ++
  s!"        if (req_we_sig) {lb}\n" ++
  s!"            uint32_t data = 0;\n" ++
  s!"            for (int i = 0; i < 32; i++) data |= (*req_data_sigs[i] ? 1u : 0u) << i;\n" ++
  s!"            if (addr == TOHOST_ADDR) {lb}\n" ++
  s!"                ds.test_done = true;\n" ++
  s!"                ds.test_data = data;\n" ++
  (match cfg.putcharAddr with
   | some _ =>
     s!"            {rb} else if (addr == PUTCHAR_ADDR) {lb}\n" ++
     s!"                putchar(data & 0xFF);\n"
   | none => "") ++
  s!"            {rb} else {lb}\n" ++
  s!"                uint32_t widx = addr >> 2;\n" ++
  s!"                if (widx < MEM_SIZE_WORDS) {lb}\n" ++
  s!"                    // Byte-enable store based on size: 00=byte, 01=half, 10=word\n" ++
  s!"                    uint32_t size = 2; // default word\n" ++
  s!"                    if (req_size_sigs) {lb}\n" ++
  s!"                        size = (*req_size_sigs[0] ? 1u : 0u)\n" ++
  s!"                             | (*req_size_sigs[1] ? 2u : 0u);\n" ++
  s!"                    {rb}\n" ++
  s!"                    uint32_t cur = mem[widx];\n" ++
  s!"                    uint32_t byte_off = addr & 3;\n" ++
  s!"                    if (size == 0) {lb} // SB\n" ++
  s!"                        uint32_t shift = byte_off * 8;\n" ++
  s!"                        cur = (cur & ~(0xFFu << shift)) | ((data & 0xFF) << shift);\n" ++
  s!"                    {rb} else if (size == 1) {lb} // SH\n" ++
  s!"                        uint32_t shift = (byte_off & 2) * 8;\n" ++
  s!"                        cur = (cur & ~(0xFFFFu << shift)) | ((data & 0xFFFF) << shift);\n" ++
  s!"                    {rb} else {lb} // SW\n" ++
  s!"                        cur = data;\n" ++
  s!"                    {rb}\n" ++
  s!"                    mem[widx] = cur;\n" ++
  s!"                {rb}\n" ++
  s!"            {rb}\n" ++
  s!"        {rb} else {lb}\n" ++
  s!"            uint32_t ridx = addr >> 2;\n" ++
  s!"            ds.read_data = (ridx < MEM_SIZE_WORDS) ? mem[ridx] : 0;\n" ++
  s!"            ds.pending = true;\n" ++
  s!"        {rb}\n" ++
  s!"    {rb}\n" ++
  s!"{rb}\n\n" ++

  s!"int main(int argc, char* argv[]) {lb}\n" ++
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

  "    // Create signals (all plain bool)\n" ++
  s!"    bool {resetName}_sig = false;\n" ++
  signalDecls ++ "\n\n" ++

  "    // Signal arrays for bus helpers\n" ++
  signalArrayDecls ++ "\n\n" ++

  "    // Port pointer array (order matches cpu_setup port binding)\n" ++
  s!"    bool* cpu_ports[] = {lb}{portPtrArray}{rb};\n\n" ++

  "    // Create and bind CPU via setup module\n" ++
  s!"    CpuCtx* ctx = cpu_create(\"u_cpu\", &{resetName}_sig,\n" ++
  s!"        cpu_ports, {portList.length});\n\n" ++

  "    // Constants\n" ++
  constBindings ++ "\n\n" ++

  "    // Memory model state\n" ++
  "    DmemState dmem_state;\n\n" ++

  "    // ========================================================================\n" ++
  "    // Manual simulation loop\n" ++
  "    // ========================================================================\n" ++
  "    printf(\"Simulation started (timeout=%u)\\n\", timeout);\n\n" ++

  "    // Helper lambda: settle combinational logic\n" ++
  s!"    auto settle = [&]() {lb}\n" ++
  s!"        for (int i = 0; i < 10; i++) {lb}\n" ++
  s!"            imem_update({pcSig}_sigs, {imemDataIn}_sigs);\n" ++
  s!"            cpu_eval_comb_all(ctx);\n" ++
  s!"        {rb}\n" ++
  s!"    {rb};\n\n" ++

  "    // Reset phase: hold reset high for 5 cycles\n" ++
  s!"    {resetName}_sig = true;\n" ++
  s!"    {dmemReady}_sig = true;\n" ++
  s!"    for (uint32_t cyc = 0; cyc < 5; cyc++) {lb}\n" ++
  "        cpu_eval_seq_all(ctx);\n" ++
  "        settle();\n" ++
  s!"    {rb}\n" ++
  s!"    {resetName}_sig = false;\n" ++
  "    settle();  // settle after de-asserting reset\n\n" ++

  "    // Main simulation loop\n" ++
  s!"    for (uint32_t cyc = 0; cyc < timeout; cyc++) {lb}\n" ++
  "        // 1. Sample dmem (reads settled combinational outputs from previous cycle)\n" ++
  s!"        dmem_tick(dmem_state,\n" ++
  s!"            {dmemValid}_sig, {dmemWe}_sig,\n" ++
  s!"            {dmemReady}_sig, {dmemRespValid}_sig,\n" ++
  s!"            {dmemAddr}_sigs, {dmemDataOut}_sigs,\n" ++
  s!"            {dmemRespData}_sigs" ++
  (match dmemSize with
   | some sizeName => s!",\n            {sizeName}_sigs"
   | none => "") ++
  ");\n\n" ++
  "        // 2. Advance CPU sequential elements (DFFs sample current signal values)\n" ++
  "        cpu_eval_seq_all(ctx);\n\n" ++
  "        // 3. Settle combinational logic (imem + CPU comb)\n" ++
  "        settle();\n\n" ++
  "        // 4. Check for test completion\n" ++
  s!"        if (dmem_state.test_done) break;\n" ++
  s!"    {rb}\n\n" ++

  s!"    printf(\"\\nTEST %s\\n\", dmem_state.test_data == 1 ? \"PASS\" : \"FAIL\");\n" ++
  s!"    printf(\"tohost: 0x%08x\\n\", dmem_state.test_data);\n" ++
  "    cpu_delete(ctx);\n" ++
  s!"    return dmem_state.test_done ? 0 : 1;\n" ++
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

def writeTestbenchCppSim (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let c := cfg.circuit
  -- Write thin setup header
  let setupH := toCpuSetupHeader c
  IO.FS.writeFile s!"{testbenchOutputDir}/cpu_setup_{c.name}.h" setupH
  -- Write heavy setup cpp (includes full module header)
  let setupCpp := toCpuSetupCpp cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/cpu_setup_{c.name}.cpp" setupCpp
  -- Write thin sim_main (no module header includes)
  let sc := toTestbenchCppSim cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/sim_main_{c.name}.cpp" sc
  IO.println s!"  ✓ sim_main_{c.name}.cpp + cpu_setup_{c.name}.cpp (testbench, split)"

def writeTestbenches (cfg : TestbenchConfig) : IO Unit := do
  Testbench.writeTestbenchSV cfg
  Testbench.writeTestbenchCppSim cfg

end Shoumei.Codegen.Testbench
