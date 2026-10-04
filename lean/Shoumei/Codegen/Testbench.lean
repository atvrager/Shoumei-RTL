/-
Codegen/Testbench.lean - Testbench Code Generation

Generates SystemVerilog and plain C++ simulation testbenches from a
TestbenchConfig. The config maps circuit ports to memory interfaces
(imem/dmem), control signals, and constants. Generators produce:

- SV testbench: module instantiation, memory model, HTIF, DPI-C loader
- C++ sim testbench: plain bool signals, manual eval loop

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

/-- A cache-line memory port: one line-wide transaction per request.  The line
    is `lineWords` 32-bit words (8 = 256 bits, the default geometry). -/
structure CacheLineMemPort where
  reqValidSignal : String     -- "mem_req_valid"
  reqAddrSignal : String      -- "mem_req_addr" (32-bit)
  reqWeSignal : String        -- "mem_req_we"
  reqDataSignal : String      -- "mem_req_data" (lineWords × 32 bits)
  respValidSignal : String    -- "mem_resp_valid"
  respDataSignal : String     -- "mem_resp_data" (lineWords × 32 bits)
  lineWords : Nat := 8
  deriving Repr

/-- Configuration for testbench generation. -/
structure TestbenchConfig where
  circuit : Circuit
  imemPort : MemoryPort
  dmemPort : MemoryPort
  /-- Cache-line memory port. When set, generates 256-bit memory model instead of
      separate imem/dmem. -/
  cacheLineMemPort : Option CacheLineMemPort := none
  memSizeWords : Nat := 16384
  tohostAddr : Nat := 0x1000
  /-- MMIO putchar address. Writes to this address emit the low byte to $write. -/
  putcharAddr : Option Nat := none
  timeoutCycles : Nat := 100000
  constantPorts : List (String × Bool) := []
  /-- Override the testbench module/file name (default: tb_<circuit.name>) -/
  tbName : Option String := none
  debugOutputs : List String := []
  /-- Spike ISA string for cosimulation (e.g. "rv32imf", "rv32im_zicsr_zifencei") -/
  spikeIsa : String := "rv32imf"
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

  -- Detect output signal groups that need individual bit ports (not bus ports)
  -- in the generated SV. Uses the same logic as the SV codegen to determine
  -- which output groups are vectorized vs individual.
  let svCtx := SystemVerilog.mkContext c
  let bitwiseOutputGroups := outputGroups.filter (fun sg =>
    SystemVerilog.outputNeedsIndividualPorts svCtx.wireToGroup svCtx.wireToIndex c sg)
  let isBitwiseBus (name : String) : Bool :=
    bitwiseOutputGroups.any (fun sg => sg.name == name)

  let signalDecls := String.intercalate "\n" (
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w) ++
    (outputSignals.filter (fun (n, _) => !isSpecial n && !isBitwiseBus n)).map (fun (n, w) => mkDecl n w)
  )

  -- Generate individual bit declarations + combined wire for bitwise output groups
  let bitwiseDeclStrs := bitwiseOutputGroups.map (fun sg =>
    let bitDecls := (List.range sg.width).map (fun i =>
      s!"  logic       {sg.name}_{i};")
    let bits := (List.range sg.width).reverse.map (fun i => s!"{sg.name}_{i}")
    let wireDecl := s!"  wire  [{sg.width - 1}:0] {sg.name} = " ++
      "{" ++ String.intercalate ", " bits ++ "};"
    String.intercalate "\n" bitDecls ++ "\n" ++ wireDecl ++ "\n")

  -- Port connections for CPU instance
  let portConns := String.intercalate ",\n" (
    [s!"      .{clockName}(clk)"] ++
    [s!"      .{resetName}({resetName})"] ++
    cfg.constantPorts.map (fun (name, value) =>
      s!"      .{name}(1'b{if value then "1" else "0"})") ++
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, _) =>
      s!"      .{n}({n})") ++
    (outputSignals.filter (fun (n, _) => !isBitwiseBus n)).map (fun (n, _) =>
      s!"      .{n}({n})") ++
    -- Add individual bit connections for bitwise output groups
    bitwiseOutputGroups.flatMap (fun sg =>
      (List.range sg.width).map (fun i =>
        s!"      .{sg.name}_{i}({sg.name}_{i})"))
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

  -- Individual bit declarations for all bitwise output groups
  let bitwiseDeclStr := String.intercalate "" bitwiseDeclStrs

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
  "    output logic [4:0]  o_fflags_acc,\n" ++
  "    // Kanata pipeline trace outputs\n" ++
  "    output logic        o_trace_alloc_valid,\n" ++
  "    output logic [3:0]  o_trace_alloc_idx,\n" ++
  "    output logic [5:0]  o_trace_alloc_physrd,\n" ++
  "    output logic        o_trace_cdb_valid,\n" ++
  "    output logic [5:0]  o_trace_cdb_tag,\n" ++
  "    output logic        o_trace_flush,\n" ++
  "    output logic [3:0]  o_trace_head_idx,\n" ++
  "    // Kanata dispatch tracking\n" ++
  "    output logic        o_trace_dispatch_int,\n" ++
  "    output logic [5:0]  o_trace_dispatch_int_tag,\n" ++
  "    output logic        o_trace_dispatch_mem,\n" ++
  "    output logic [5:0]  o_trace_dispatch_mem_tag,\n" ++
  "    output logic        o_trace_dispatch_branch,\n" ++
  "    output logic [5:0]  o_trace_dispatch_branch_tag,\n" ++
  "    output logic        o_trace_dispatch_muldiv,\n" ++
  "    output logic [5:0]  o_trace_dispatch_muldiv_tag,\n" ++
  "    output logic        o_trace_dispatch_fp,\n" ++
  "    output logic [5:0]  o_trace_dispatch_fp_tag\n" ++
  ");\n\n" ++
  "  // =========================================================================\n" ++
  "  // CPU I/O signals\n" ++
  "  // =========================================================================\n" ++
  signalDecls ++ "\n" ++
  bitwiseDeclStr ++ "\n" ++
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
  "  // DPI-C: read a memory word, so the cosimulation can compare the RTL\n" ++
  "  // memory against the reference model.\n" ++
  "  export \"DPI-C\" function dpi_mem_read;\n" ++
  "  function int unsigned dpi_mem_read(input int unsigned word_addr);\n" ++
  "    return mem[word_addr];\n" ++
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
     "  endfunction\n\n" ++
     "  import \"DPI-C\" function void dpi_uart_tx_byte(input byte data);\n\n"
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

  "  // Cosim memory-write observation.  The driver reads the counter every\n" ++
  "  // cycle; when it changes, it compares the word just written against the\n" ++
  "  // reference model, which names the store whose effect differs.\n" ++
  "  logic [31:0] mem_wr_count;\n" ++
  "  logic [31:0] mem_wr_idx;\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      mem_wr_count <= 32'b0;\n" ++
  "      mem_wr_idx   <= 32'b0;\n" ++
  s!"    end else if ({dmemValid} && {dmemWe}) begin\n" ++
  "      mem_wr_count <= mem_wr_count + 32'b1;\n" ++
  s!"      mem_wr_idx   <= addr_to_idx({dmemAddr});\n" ++
  "    end\n" ++
  "  end\n\n" ++
  "  export \"DPI-C\" function dpi_mem_wr_count;\n" ++
  "  function int unsigned dpi_mem_wr_count();\n" ++
  "    return mem_wr_count;\n" ++
  "  endfunction\n\n" ++
  "  export \"DPI-C\" function dpi_mem_wr_idx;\n" ++
  "  function int unsigned dpi_mem_wr_idx();\n" ++
  "    return mem_wr_idx;\n" ++
  "  endfunction\n\n" ++
  "  export \"DPI-C\" function dpi_mem_wr_words;\n" ++
  "  function int unsigned dpi_mem_wr_words();\n" ++
  "    return 1;\n" ++
  "  endfunction\n\n" ++

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
     "  // MMIO putchar & UART: writes to PUTCHAR_ADDR or 0x10000000 emit a character\n" ++
     "  // =========================================================================\n" ++
     s!"  always_ff @(posedge clk) begin\n" ++
     s!"    if (!{resetName} && {dmemValid} && {dmemWe} && ({dmemAddr} == putchar_addr_r || {dmemAddr} == 32'h10000000)) begin\n" ++
     s!"      $write(\"%c\", {dmemDataOut}[7:0]);\n" ++
     s!"      dpi_uart_tx_byte({dmemDataOut}[7:0]);\n" ++
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
  "  assign o_fflags_acc      = fflags_acc;\n" ++
  "  assign o_trace_alloc_valid = trace_alloc_valid;\n" ++
  "  assign o_trace_alloc_idx   = trace_alloc_idx;\n" ++
  "  assign o_trace_alloc_physrd = trace_alloc_physrd;\n" ++
  "  assign o_trace_cdb_valid   = trace_cdb_valid;\n" ++
  "  assign o_trace_cdb_tag     = trace_cdb_tag;\n" ++
  "  assign o_trace_flush       = trace_flush;\n" ++
  "  assign o_trace_head_idx    = trace_head_idx;\n" ++
  "  assign o_trace_dispatch_int        = trace_dispatch_int;\n" ++
  "  assign o_trace_dispatch_int_tag    = trace_dispatch_int_tag;\n" ++
  "  assign o_trace_dispatch_mem        = trace_dispatch_mem;\n" ++
  "  assign o_trace_dispatch_mem_tag    = trace_dispatch_mem_tag;\n" ++
  "  assign o_trace_dispatch_branch     = trace_dispatch_branch;\n" ++
  "  assign o_trace_dispatch_branch_tag = trace_dispatch_branch_tag;\n" ++
  "  assign o_trace_dispatch_muldiv        = trace_dispatch_muldiv;\n" ++
  "  assign o_trace_dispatch_muldiv_tag    = trace_dispatch_muldiv_tag;\n" ++
  "  assign o_trace_dispatch_fp         = trace_dispatch_fp;\n" ++
  "  assign o_trace_dispatch_fp_tag     = trace_dispatch_fp_tag;\n\n" ++
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

/-- Generate the thin header for CPU setup. -/
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
  "void cpu_eval_seq_sample_all(CpuCtx* ctx);\n" ++
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
  s!"void cpu_eval_seq_sample_all(CpuCtx* ctx) {lb}\n" ++
  s!"    static_cast<{c.name}*>(ctx->cpu)->eval_seq_sample_all();\n" ++
  s!"{rb}\n\n" ++
  s!"void cpu_eval_seq_all(CpuCtx* ctx) {lb}\n" ++
  s!"    static_cast<{c.name}*>(ctx->cpu)->eval_seq_all();\n" ++
  s!"{rb}\n"

/-- Generate a plain C++ simulation testbench. -/
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
  s!"    bool snap_req_valid, bool snap_req_we,\n" ++
  s!"    uint32_t snap_addr, uint32_t snap_data, uint32_t snap_size,\n" ++
  s!"    bool& req_ready_sig, bool& resp_valid_sig,\n" ++
  s!"    bool** resp_data_sigs) {lb}\n" ++
  s!"    req_ready_sig = true;\n\n" ++
  s!"    // Respond to pending load from previous cycle\n" ++
  s!"    if (ds.pending) {lb}\n" ++
  s!"        resp_valid_sig = true;\n" ++
  s!"        for (int i = 0; i < 32; i++) *resp_data_sigs[i] = (ds.read_data >> i) & 1;\n" ++
  s!"        ds.pending = false;\n" ++
  s!"    {rb} else {lb}\n" ++
  s!"        resp_valid_sig = false;\n" ++
  s!"        // Keep resp_data at last read value (matches SV: assign dmem_resp_data = dmem_read_data)\n" ++
  s!"        for (int i = 0; i < 32; i++) *resp_data_sigs[i] = (ds.read_data >> i) & 1;\n" ++
  s!"    {rb}\n\n" ++
  s!"    // Handle new request\n" ++
  s!"    if (snap_req_valid) {lb}\n" ++
  s!"        uint32_t addr = snap_addr;\n" ++
  s!"        if (snap_req_we) {lb}\n" ++
  s!"            uint32_t data = snap_data;\n" ++
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
  s!"                    uint32_t size = snap_size;\n" ++
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
  "        cpu_eval_seq_sample_all(ctx);\n" ++
  "        cpu_eval_seq_all(ctx);\n" ++
  "        settle();\n" ++
  s!"    {rb}\n" ++
  s!"    {resetName}_sig = false;\n" ++
  "    settle();  // settle after de-asserting reset\n\n" ++

  "    // Main simulation loop\n" ++
  s!"    for (uint32_t cyc = 0; cyc < timeout; cyc++) {lb}\n" ++
  "        // 1. Snapshot dmem inputs (both always_ff blocks must see same pre-edge state)\n" ++
  s!"        bool snap_req_valid = {dmemValid}_sig;\n" ++
  s!"        bool snap_req_we = {dmemWe}_sig;\n" ++
  s!"        uint32_t snap_addr = 0;\n" ++
  s!"        for (int i = 0; i < 32; i++) snap_addr |= (*{dmemAddr}_sigs[i] ? 1u : 0u) << i;\n" ++
  s!"        uint32_t snap_data = 0;\n" ++
  s!"        for (int i = 0; i < 32; i++) snap_data |= (*{dmemDataOut}_sigs[i] ? 1u : 0u) << i;\n" ++
  s!"        uint32_t snap_size = 2;\n" ++
  (match dmemSize with
   | some sizeName => s!"        snap_size = (*{sizeName}_sigs[0] ? 1u : 0u) | (*{sizeName}_sigs[1] ? 2u : 0u);\n"
   | none => "") ++
  "\n" ++
  "        // 2. Two-phase DFF evaluation: sample all d inputs, then update all q outputs\n" ++
  "        cpu_eval_seq_sample_all(ctx);\n" ++
  "        cpu_eval_seq_all(ctx);\n\n" ++
  "        // 3. Process dmem with snapshotted inputs (registered response like SV always_ff)\n" ++
  s!"        dmem_tick(dmem_state,\n" ++
  s!"            snap_req_valid, snap_req_we, snap_addr, snap_data, snap_size,\n" ++
  s!"            {dmemReady}_sig, {dmemRespValid}_sig,\n" ++
  s!"            {dmemRespData}_sigs);\n\n" ++
  "        // 4. Settle combinational logic (imem + CPU comb)\n" ++
  "        settle();\n\n" ++
  "        // 5. Check for test completion\n" ++
  s!"        if (dmem_state.test_done) break;\n" ++
  s!"    {rb}\n\n" ++

  s!"    printf(\"\\nTEST %s\\n\", dmem_state.test_data == 1 ? \"PASS\" : \"FAIL\");\n" ++
  s!"    printf(\"tohost: 0x%08x\\n\", dmem_state.test_data);\n" ++
  "    cpu_delete(ctx);\n" ++
  s!"    return dmem_state.test_done ? 0 : 1;\n" ++
  s!"{rb}\n"

/-! ## Cache-Line Memory SV Testbench Generator -/

/-- Generate SV testbench for a cached CPU with 256-bit cache-line memory interface. -/
def toTestbenchSVCached (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let inputGroups := SystemVerilog.autoDetectSignalGroups c.inputs
  let outputGroups := SystemVerilog.autoDetectSignalGroups c.outputs

  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let _clockName := if clockWires.isEmpty then "clock" else Wire.name (List.head! clockWires)
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)

  let inputBusWireNames := inputGroups.flatMap (fun sg => sg.wires.map Wire.name)
  let outputBusWireNames := outputGroups.flatMap (fun sg => sg.wires.map Wire.name)

  let inputSignals : List (String × Nat) :=
    let scalars := c.inputs.filter (fun w => !inputBusWireNames.contains w.name)
    scalars.map (fun w => (w.name, 1)) ++ inputGroups.map (fun sg => (sg.name, sg.width))

  let outputSignals : List (String × Nat) :=
    let scalars := c.outputs.filter (fun w => !outputBusWireNames.contains w.name)
    scalars.map (fun w => (w.name, 1)) ++ outputGroups.map (fun sg => (sg.name, sg.width))

  let isSpecial (name : String) : Bool :=
    name == _clockName || name == resetName ||
    cfg.constantPorts.any (fun (cn, _) => cn == name)

  let mkDecl (name : String) (width : Nat) : String :=
    if width > 1 then s!"  logic [{width-1}:0] {name};"
    else s!"  logic        {name};"

  let signalDecls := String.intercalate "\n" (
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w) ++
    (outputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, w) => mkDecl n w)
  )

  let portConns := String.intercalate ",\n" (
    [s!"      .{_clockName}(clk)"] ++
    [s!"      .{resetName}({resetName})"] ++
    cfg.constantPorts.map (fun (name, value) =>
      s!"      .{name}(1'b{if value then "1" else "0"})") ++
    (inputSignals.filter (fun (n, _) => !isSpecial n)).map (fun (n, _) =>
      s!"      .{n}({n})") ++
    outputSignals.map (fun (n, _) =>
      s!"      .{n}({n})")
  )

  let clmp := cfg.cacheLineMemPort.getD {
    reqValidSignal := "mem_req_valid"
    reqAddrSignal := "mem_req_addr"
    reqWeSignal := "mem_req_we"
    reqDataSignal := "mem_req_data"
    respValidSignal := "mem_resp_valid"
    respDataSignal := "mem_resp_data"
  }

  let memSizeStr := toString cfg.memSizeWords
  let timeoutStr := toString cfg.timeoutCycles
  let tohostHex := hexLit 32 cfg.tohostAddr
  let putcharParam := match cfg.putcharAddr with
    | some addr => s!",\n    parameter PUTCHAR_ADDR    = {hexLit 32 addr}"
    | none => ""

  let tbName := optOrDefault cfg.tbName s!"tb_{c.name}"
  let rdDataWidth := (outputGroups.find? (·.name == "rvvi_rdd_0")).map (·.width) |>.getD 32
  let fpRdDataWidth := (outputGroups.find? (·.name == "rvvi_fprd")).map (·.width) |>.getD 64
  let snoopDataWidth := (outputGroups.find? (·.name == "store_snoop_data")).map (·.width) |>.getD 32

  "//==============================================================================\n" ++
  s!"// {tbName}.sv - Auto-generated testbench for {c.name} (cache-line memory)\n" ++
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
  "    output logic [31:0] o_cycle_count,\n" ++
  "    output logic        o_rob_empty,\n" ++
  "    // Memory request observation\n" ++
  "    output logic        o_mem_req_valid,\n" ++
  "    output logic        o_mem_req_we,\n" ++
  "    output logic [31:0] o_mem_req_addr,\n" ++
  "    // Writeback observation: which lane presented what, for a mismatch.\n" ++
  "    output logic        o_lsu_valid,\n" ++
  "    output logic [5:0]  o_lsu_tag,\n" ++
  "    output logic [63:0] o_lsu_data,\n" ++
  "    output logic        o_dmem_valid,\n" ++
  "    output logic [5:0]  o_dmem_tag,\n" ++
  "    output logic [63:0] o_dmem_data,\n" ++
  "    output logic        o_aw_pending,\n" ++
  "    output logic [63:0] o_fp_busy,\n" ++
  "    output logic        o_commit_ready,\n" ++
  "    output logic        o_fp_busy_eu,\n" ++
  "    output logic        o_div_busy,\n" ++
  "    output logic [5:0]  o_fp_dest_tag,\n" ++
  "    output logic [5:0]  o_fp_s1_tag,\n" ++
  "    output logic [5:0]  o_fp_s2_tag,\n" ++
  "    output logic        o_fp_s1_ready,\n" ++
  "    output logic        o_fp_s2_ready,\n" ++
  "    output logic        o_fp_dispatch_en,\n" ++
  "    output logic        o_fp_avail,\n" ++
  "    output logic        o_fp_disp_valid,\n" ++
  "    output logic        o_flush_rs_fp,\n" ++
  "    output logic        o_fp_disp_pre,\n" ++
  "    output logic        o_fp_ren_valid,\n" ++
  "    output logic        o_dispatch_stall,\n" ++
  "    output logic        o_rename_ext_stall,\n" ++
  "    output logic        o_rename_supp_stall,\n" ++
  "    output logic        o_rob_full,\n" ++
  "    output logic        o_fence_i_suppress,\n" ++
  "    output logic        o_csr_rename_en,\n" ++
  "    output logic        o_suppress_all,\n" ++
  "    output logic        o_trap_or_mret_det,\n" ++
  "    output logic        o_stall_rr,\n" ++
  "    output logic        o_stall_req_rs0,\n" ++
  "    output logic        o_redirect_or,\n" ++
  "    output logic        o_pipeline_flush,\n" ++
  "    output logic        o_dmem_stall_ext,\n" ++
  "    output logic        o_fetch_stall_ext,\n" ++
  "    output logic        o_fp_drain_mode,\n" ++
  "    output logic        o_fp_stale_suppress,\n" ++
  "    output logic        o_fp_valid_out,\n" ++
  "    output logic        o_fp_enq_valid_gated,\n" ++
  "    output logic        o_fp_drain_hold,\n" ++
  "    output logic        o_fallback_cdb_inject,\n" ++
  "    output logic        o_all_cdb_inject,\n" ++
  "    output logic        o_cdb_valid_fp_prf,\n" ++
  "    output logic        o_d0_base_tmp,\n" ++
  "    output logic        o_d0_base_pre,\n" ++
  "    output logic        o_rs_e0_valid,\n" ++
  "    output logic        o_rs_e1_valid,\n" ++
  "    output logic        o_rs_e0_ready,\n" ++
  "    output logic        o_rs_e1_ready,\n" ++
  "    output logic        o_lsu_sb_empty,\n" ++
  "    output logic        o_lsu_sb_deq_valid,\n" ++
  "    output logic        o_commit_store_en,\n" ++
  "    output logic [63:0] o_dbg_sb,\n" ++
  "    output logic [31:0] o_dbg_amo,\n" ++
  "    output logic [63:0] o_dbg_csr,\n" ++
  "    output logic [63:0] o_dbg_atm,\n" ++
  "    output logic [63:0] o_dbg_atmf,\n" ++
  "    output logic [31:0] o_dbg_atmf2,\n" ++
  "    output logic [63:0] o_dbg_ren,\n" ++
  "    output logic [63:0] o_dbg_ren2,\n" ++
  "    output logic [63:0] o_dbg_cdbd,\n" ++
  "    output logic        o_hw_draining_reg,\n" ++
  "    output logic        o_fence_start_delayed,\n" ++
  "    output logic        o_lsu_sb_full,\n" ++
  "    output logic        o_lsu_sb_flush_pending,\n" ++
  "    output logic        o_fi_start_nocsr,\n" ++
  "    output logic        o_fence_i_draining,\n" ++
  "    output logic        o_d0_needs_sb,\n" ++
  "    output logic        o_hw_suppress,\n" ++
  "    output logic        o_useq_active,\n" ++
  "    output logic        o_fallback_active,\n" ++
  "    output logic        o_stall_req_im,\n" ++
  "    output logic        o_stall_req_bm,\n" ++
  "    output logic        o_fp_stall_req_0,\n" ++
  "    output logic        o_sb_stall_req_0,\n" ++
  "    output logic        o_suppress_pre,\n" ++
  "    output logic        o_dmem_we,\n" ++
  "    output logic        o_dmem_req_v,\n" ++
  "    output logic [31:0] o_req_addr,\n" ++
  "    output logic [63:0] o_req_data,\n" ++
  "    output logic [1:0]  o_req_size,\n" ++
  "    output logic        o_sb_deq_v,\n" ++
  "    output logic        o_sb_empty,\n" ++
  "    output logic        o_sb_full,\n" ++
  "    output logic        o_load_pending,\n" ++
  "    output logic        o_aw_pend,\n" ++
  "    output logic [31:0] o_sb_cnt,\n" ++
  "    output logic [63:0] o_load_addr,\n" ++
  "    output logic [1:0]  o_load_size,\n" ++
  "    // HTIF\n" ++
  "    output logic [31:0] o_tohost,\n" ++
  "    // RVVI-TRACE outputs (dual-retire W=2 cosimulation)\n" ++
  "    output logic        o_rvvi_valid_0,\n" ++
  "    output logic        o_rvvi_valid_1,\n" ++
  "    output logic        o_rvvi_trap_0,\n" ++
  "    output logic        o_rvvi_trap_1,\n" ++
  "    output logic [31:0] o_rvvi_pc_rdata_0,\n" ++
  "    output logic [31:0] o_rvvi_pc_rdata_1,\n" ++
  "    output logic [31:0] o_rvvi_insn_0,\n" ++
  "    output logic [31:0] o_rvvi_insn_1,\n" ++
  "    output logic [4:0]  o_rvvi_rd_0,\n" ++
  "    output logic [4:0]  o_rvvi_rd_1,\n" ++
  "    output logic        o_rvvi_rd_valid_0,\n" ++
  "    output logic        o_rvvi_rd_valid_1,\n" ++
  s!"    output logic [{rdDataWidth-1}:0] o_rvvi_rd_data_0,\n" ++
  s!"    output logic [{rdDataWidth-1}:0] o_rvvi_rd_data_1,\n" ++
  "    // register-class coverage: which file was written, and the FP flags\n" ++
  "    output logic        o_rvvi_is_fp_0,\n" ++
  "    output logic        o_rvvi_is_fp_1,\n" ++
  "    output logic [4:0]  o_rvvi_fflags_0,\n" ++
  "    output logic [4:0]  o_rvvi_fflags_slot1,\n" ++
  s!"    output logic [{fpRdDataWidth-1}:0] o_rvvi_fp_rd_data,\n" ++
  s!"    output logic [{fpRdDataWidth-1}:0] o_rvvi_fp_rd_data_slot1\n" ++
  ");\n\n" ++

  "  // =========================================================================\n" ++
  "  // DUT I/O signals\n" ++
  "  // =========================================================================\n" ++
  signalDecls ++ "\n" ++
  s!"  logic        {resetName};\n" ++
  s!"  assign {resetName} = ~rst_n;\n\n" ++

  "  // =========================================================================\n" ++
  "  // DUT instance\n" ++
  "  // =========================================================================\n" ++
  s!"  {c.name} u_cpu (\n" ++
  portConns ++ "\n" ++
  "  );\n\n" ++

  "  // =========================================================================\n" ++
  "  // Memory: 256-bit cache-line interface, 1-cycle latency\n" ++
  "  // =========================================================================\n" ++
  "  logic [31:0] mem [0:MEM_SIZE_WORDS-1];\n\n" ++
  "  // DPI-C: allow C++ to write memory words before simulation starts\n" ++
  "  export \"DPI-C\" function dpi_mem_write;\n" ++
  "  function void dpi_mem_write(input int unsigned word_addr, input int unsigned data);\n" ++
  "    mem[word_addr] = data;\n" ++
  "  endfunction\n\n" ++
  "  // DPI-C: read a memory word, so the cosimulation can compare the RTL\n" ++
  "  // memory against the reference model.\n" ++
  "  export \"DPI-C\" function dpi_mem_read;\n" ++
  "  function int unsigned dpi_mem_read(input int unsigned word_addr);\n" ++
  "    return mem[word_addr];\n" ++
  "  endfunction\n\n" ++
  "  // DPI-C: override HTIF address from ELF symbol\n" ++
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
     "  endfunction\n\n" ++
     "  import \"DPI-C\" function void dpi_uart_tx_byte(input byte data);\n\n"
   | none => "") ++
  "  localparam logic [31:0] MEM_BASE = 32'h00000000;\n\n" ++
  "  function automatic logic [31:0] addr_to_idx(input logic [31:0] addr);\n" ++
  "    return (addr - MEM_BASE) >> 2;\n" ++
  "  endfunction\n\n" ++

  "  // --- Cache-line memory: 1-cycle read latency, combinational write ---\n" ++
  "  logic        mem_pending;\n" ++
  s!"  logic [{clmp.lineWords * 32 - 1}:0] mem_read_line;\n\n" ++
  s!"  wire [31:0] mem_line_idx = addr_to_idx({clmp.reqAddrSignal});\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  s!"      {clmp.respValidSignal} <= 1'b0;\n" ++
  s!"      mem_read_line  <= {clmp.lineWords * 32}'b0;\n" ++
  "      mem_pending    <= 1'b0;\n" ++
  "    end else begin\n" ++
  "      mem_pending    <= 1'b0;\n" ++
  s!"      {clmp.respValidSignal} <= 1'b0;\n\n" ++
  s!"      if ({clmp.reqValidSignal}) begin\n" ++
  s!"        if ({clmp.reqWeSignal}) begin\n" ++
  s!"          // Write the whole cache line (line-aligned address)\n" ++
  String.join ((List.range clmp.lineWords).map fun w =>
    s!"          mem[mem_line_idx + {w}] <= {clmp.reqDataSignal}[{w * 32 + 31}:{w * 32}];\n") ++
  "        end else begin\n" ++
  "          // Read the whole cache line (line-aligned address)\n" ++
  "          mem_read_line <= {\n" ++
  String.join ((List.range clmp.lineWords).reverse.map fun w =>
    s!"            mem[mem_line_idx + {w}]{if w == 0 then "\n" else ",\n"}") ++
  "          };\n" ++
  "          mem_pending <= 1'b1;\n" ++
  "        end\n" ++
  "      end\n\n" ++
  "      if (mem_pending) begin\n" ++
  s!"        {clmp.respValidSignal} <= 1'b1;\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++
  "  // Cosim memory-write observation.  The driver reads the counter every\n" ++
  "  // cycle; when it changes, it compares the words just written against the\n" ++
  "  // reference model, which names the store whose effect differs.\n" ++
  "  logic [31:0] mem_wr_count;\n" ++
  "  logic [31:0] mem_wr_idx;\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      mem_wr_count <= 32'b0;\n" ++
  "      mem_wr_idx   <= 32'b0;\n" ++
  "    end else if (" ++ clmp.reqValidSignal ++ " && " ++ clmp.reqWeSignal ++ ") begin\n" ++
  "      mem_wr_count <= mem_wr_count + 32'b1;\n" ++
  "      mem_wr_idx   <= mem_line_idx;\n" ++
  "    end\n" ++
  "  end\n\n" ++
  "  export \"DPI-C\" function dpi_mem_wr_count;\n" ++
  "  function int unsigned dpi_mem_wr_count();\n" ++
  "    return mem_wr_count;\n" ++
  "  endfunction\n\n" ++
  "  export \"DPI-C\" function dpi_mem_wr_idx;\n" ++
  "  function int unsigned dpi_mem_wr_idx();\n" ++
  "    return mem_wr_idx;\n" ++
  "  endfunction\n\n" ++
  "  export \"DPI-C\" function dpi_mem_wr_words;\n" ++
  "  function int unsigned dpi_mem_wr_words();\n" ++
  s!"    return {clmp.lineWords};\n" ++
  "  endfunction\n\n" ++
  "  // =========================================================================\n" ++
  "  // CLINT: Machine Timer (mtime, mtimecmp, mtip)\n" ++
  "  // =========================================================================\n" ++
  "  logic [63:0] mtime;\n" ++
  "  logic [63:0] mtimecmp;\n" ++
  "  wire         mtip = (mtime >= mtimecmp);\n" ++
  "  assign       mtip_in = mtip;\n" ++
  "  assign       msip_in = 1'b0;\n" ++
  "  assign       meip_in = 1'b0;\n\n" ++
  "  // CLINT MMIO addresses\n" ++
  "  localparam logic [31:0] CLINT_MTIMECMP_LO = 32'h02004000;\n" ++
  "  localparam logic [31:0] CLINT_MTIMECMP_HI = 32'h02004004;\n" ++
  "  localparam logic [31:0] CLINT_MTIME_LO    = 32'h0200BFF8;\n" ++
  "  localparam logic [31:0] CLINT_MTIME_HI    = 32'h0200BFFC;\n\n" ++
  "  wire clint_mtimecmp_lo_wr = store_snoop_valid && (store_snoop_addr == CLINT_MTIMECMP_LO);\n" ++
  "  wire clint_mtimecmp_hi_wr = store_snoop_valid && (store_snoop_addr == CLINT_MTIMECMP_HI);\n" ++
  "  wire clint_mtime_lo_wr    = store_snoop_valid && (store_snoop_addr == CLINT_MTIME_LO);\n" ++
  "  wire clint_mtime_hi_wr    = store_snoop_valid && (store_snoop_addr == CLINT_MTIME_HI);\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      mtime    <= 64'b0;\n" ++
  "      mtimecmp <= 64'hFFFFFFFFFFFFFFFF;\n" ++
  "    end else begin\n" ++
  "      mtime <= mtime + 1;\n" ++
  (if snoopDataWidth >= 64 then
    "      if (clint_mtimecmp_lo_wr) begin\n" ++
    "        mtimecmp[31:0]  <= store_snoop_data[31:0];\n" ++
    "        mtimecmp[63:32] <= store_snoop_data[63:32];\n" ++
    "      end\n" ++
    "      if (clint_mtimecmp_hi_wr) mtimecmp[63:32] <= store_snoop_data[31:0];\n" ++
    "      if (clint_mtime_lo_wr) begin\n" ++
    "        mtime[31:0]     <= store_snoop_data[31:0];\n" ++
    "        mtime[63:32]    <= store_snoop_data[63:32];\n" ++
    "      end\n" ++
    "      if (clint_mtime_hi_wr)    mtime[63:32]    <= store_snoop_data[31:0];\n"
   else
    "      if (clint_mtimecmp_lo_wr) mtimecmp[31:0]  <= store_snoop_data;\n" ++
    "      if (clint_mtimecmp_hi_wr) mtimecmp[63:32] <= store_snoop_data;\n" ++
    "      if (clint_mtime_lo_wr)    mtime[31:0]     <= store_snoop_data;\n" ++
    "      if (clint_mtime_hi_wr)    mtime[63:32]    <= store_snoop_data;\n") ++
  "    end\n" ++
  "  end\n\n" ++
  "  // CLINT read intercept: override cache-line response for CLINT addresses\n" ++
  "  // When a cache-line read hits the CLINT region (0x02000000-0x0200FFFF),\n" ++
  "  // inject CLINT register values into the response data.\n" ++
  "  wire clint_region = (mem_req_addr_r[31:16] == 16'h0200);\n" ++
  "  logic [31:0] mem_req_addr_r;\n" ++
  "  logic        clint_pending_q1;\n" ++
  "  logic        clint_pending;\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      mem_req_addr_r  <= 32'b0;\n" ++
  "      clint_pending_q1 <= 1'b0;\n" ++
  "      clint_pending    <= 1'b0;\n" ++
  "    end else begin\n" ++
  "      // Pipeline stage 2: align clint_pending with mem_resp_valid (2-cycle latency)\n" ++
  "      clint_pending <= clint_pending_q1;\n" ++
  "      clint_pending_q1 <= 1'b0;\n" ++
  s!"      if ({clmp.reqValidSignal} && !{clmp.reqWeSignal}) begin\n" ++
  s!"        mem_req_addr_r   <= {clmp.reqAddrSignal};\n" ++
  s!"        clint_pending_q1 <= ({clmp.reqAddrSignal}[31:16] == 16'h0200);\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++
  "  // Build CLINT cache line response (8 words aligned to cache line)\n" ++
  "  logic [255:0] clint_line;\n" ++
  "  always_comb begin\n" ++
  "    clint_line = 256'b0;\n" ++
  "    case (mem_req_addr_r[15:5])  // cache-line aligned offset within CLINT\n" ++
  "      11'h200: begin  // 0x02004000 (mtimecmp)\n" ++
  "        clint_line[31:0]   = mtimecmp[31:0];\n" ++
  "        clint_line[63:32]  = mtimecmp[63:32];\n" ++
  "      end\n" ++
  "      11'h5FF: begin  // 0x0200BFE0 (mtime at offset 0x18/0x1C within line)\n" ++
  "        clint_line[223:192] = mtime[31:0];\n" ++
  "        clint_line[255:224] = mtime[63:32];\n" ++
  "      end\n" ++
  "      default: ;\n" ++
  "    endcase\n" ++
  "  end\n\n" ++
  s!"  assign {clmp.respDataSignal} = clint_pending ? clint_line : mem_read_line;\n\n" ++
  "  // =========================================================================\n" ++
  "  // HTIF: tohost termination (detected from CPU store snoop)\n" ++
  "  // =========================================================================\n" ++
  "  logic        test_done;\n" ++
  "  logic        test_pass;\n" ++
  "  logic [31:0] test_code;\n\n" ++
  "  // Monitor CPU store interface directly (bypasses cache hierarchy)\n" ++
  s!"  // A store reaches memory when the store buffer dequeues it.  A drain asserts no\n" ++
  s!"  // write-enable on the port, so store_snoop_valid cannot see it.\n" ++
  s!"  wire tohost_store = (store_snoop_valid ||\n" ++
  s!"                        u_cpu.u_cpu.lsu_sb_deq_valid ||\n" ++
  s!"                        u_cpu.u_cpu.atom_aw_pending) &&\n" ++
  s!"                       (store_snoop_addr == tohost_addr_r);\n\n" ++
  s!"  always_ff @(posedge clk or posedge {resetName}) begin\n" ++
  s!"    if ({resetName}) begin\n" ++
  "      test_done <= 1'b0;\n" ++
  "      test_pass <= 1'b0;\n" ++
  "      test_code <= 32'b0;\n" ++
  "    end else begin\n" ++
  "      if (tohost_store) begin\n" ++
  (if snoopDataWidth >= 64 then
    "        test_code <= store_snoop_data[31:0];\n" ++
    "        test_pass <= (store_snoop_data[31:0] == 32'h1);\n"
   else
    "        test_code <= store_snoop_data;\n" ++
    "        test_pass <= (store_snoop_data == 32'h1);\n") ++
  "        test_done <= 1'b1;\n" ++
  "      end\n" ++
  "    end\n" ++
  "  end\n\n" ++

  -- MMIO putchar: also monitor cache-line writes for putchar address
  (match cfg.putcharAddr with
   | some _ =>
     "  // =========================================================================\n" ++
     "  // MMIO putchar & UART: monitor CPU store snoop for putchar / UART TX address\n" ++
     "  // =========================================================================\n" ++
     "  wire is_uart_store = store_snoop_valid && (store_snoop_addr == 32'h10000000);\n" ++
     "  wire is_putchar_store = store_snoop_valid && (store_snoop_addr == putchar_addr_r);\n" ++
     "  wire putchar_store = is_uart_store || is_putchar_store;\n\n" ++
     s!"  always_ff @(posedge clk) begin\n" ++
     s!"    if (!{resetName} && putchar_store) begin\n" ++
     "      $write(\"%c\", store_snoop_data[7:0]);\n" ++
     "      dpi_uart_tx_byte(store_snoop_data[7:0]);\n" ++
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
  "  // Output assignments\n" ++
  "  // =========================================================================\n" ++
  "  assign o_test_done       = test_done;\n" ++
  "  assign o_test_pass       = test_pass;\n" ++
  "  assign o_test_code       = test_code;\n" ++
  "  assign o_cycle_count     = cycle_count;\n" ++
  "  assign o_rob_empty       = rob_empty;\n" ++
  s!"  assign o_mem_req_valid  = {clmp.reqValidSignal};\n" ++
  s!"  assign o_mem_req_we     = {clmp.reqWeSignal};\n" ++
  s!"  assign o_mem_req_addr   = {clmp.reqAddrSignal};\n" ++
  "  assign o_lsu_valid       = u_cpu.u_cpu.lsu_valid;\n" ++
  "  assign o_lsu_tag         = u_cpu.u_cpu.lsu_tag;\n" ++
  "  assign o_lsu_data        = u_cpu.u_cpu.lsu_data;\n" ++
  "  assign o_dmem_valid      = u_cpu.u_cpu.dmem_valid_gated;\n" ++
  "  assign o_dmem_tag        = u_cpu.u_cpu.dmem_load_tag_reg;\n" ++
  "  assign o_dmem_data       = u_cpu.u_cpu.dmem_resp_fmt;\n" ++
  "  assign o_aw_pending      = u_cpu.u_cpu.atom_aw_pending;\n" ++
  "  // A hang leaves no mismatch behind, so the state that caused it has to be\n" ++
  "  // readable at the timeout: which floating-point registers are still marked\n" ++
  "  // busy, and whether the ROB head is complete.\n" ++
  "  assign o_fp_busy         = 64'b0;\n" ++
  "  assign o_commit_ready    = u_cpu.u_cpu.commit_ready[0];\n" ++
  "  // These were hardwired to zero: the floating-point execution unit reports\n" ++
  "  // busy, which gates the station, so a stuck busy bit stops all FP dispatch.\n" ++
  "  assign o_fp_busy_eu      = u_cpu.u_cpu.fp_busy_eu;\n" ++
  "  assign o_div_busy        = 1'b0;\n" ++
  "  // What the floating-point reservation station wants to issue, and whether\n" ++
  "  // it believes its operands have arrived.  A source the scoreboard has free\n" ++
  "  // but the station calls not-ready is a scheduler defect, not a stall.\n" ++
  "  assign o_fp_dest_tag     = u_cpu.u_cpu.fp_issue_dest_tag;\n" ++
  "  assign o_fp_s1_tag       = u_cpu.u_cpu.fp_issue_src1_tag;\n" ++
  "  assign o_fp_s2_tag       = u_cpu.u_cpu.fp_issue_src2_tag;\n" ++
  "  assign o_fp_s1_ready     = u_cpu.u_cpu.fp_issue_src1_ready;\n" ++
  "  assign o_fp_s2_ready     = u_cpu.u_cpu.fp_issue_src2_ready;\n" ++
  "  assign o_fp_dispatch_en  = u_cpu.u_cpu.fp_rs_dispatch_en;\n" ++
  "  // A station with no free slot and a flush that never arrives is a different\n" ++
  "  // stall from one that holds an entry it cannot issue.\n" ++
  "  assign o_fp_avail        = u_cpu.u_cpu.rs_fp_avail_0;\n" ++
  "  assign o_fp_disp_valid   = u_cpu.u_cpu.rs_fp_dispatch_valid;\n" ++
  "  assign o_flush_rs_fp     = u_cpu.u_cpu.flush_rs_fp;\n" ++
  "  // The station's dispatch input is issue_en (driven by the rename decode),\n" ++
  "  // not dispatch_valid, which is the station's own issue-ready output.\n" ++
  "  assign o_fp_disp_pre     = u_cpu.u_cpu.fp_dispatch_valid_pre;\n" ++
  "  assign o_fp_ren_valid    = u_cpu.u_cpu.fp_rename_dispatch_valid;\n" ++
  "  assign o_dispatch_stall  = u_cpu.u_cpu.dispatch_stall;\n" ++
  "  assign o_rename_ext_stall= u_cpu.u_cpu.rename_ext_stall;\n" ++
  "  assign o_rename_supp_stall = u_cpu.u_cpu.rename_supp_stall;\n" ++
  "  assign o_rob_full        = u_cpu.u_cpu.rob_full;\n" ++
  "  assign o_fence_i_suppress = u_cpu.u_cpu.fence_i_suppress;\n" ++
  "  assign o_csr_rename_en = u_cpu.u_cpu.csr_rename_en;\n" ++
  "  assign o_suppress_all = u_cpu.u_cpu.suppress_all;\n" ++
  "  assign o_trap_or_mret_det = u_cpu.u_cpu.trap_or_mret_det;\n" ++
  "  assign o_stall_rr = u_cpu.u_cpu.stall_rr;\n" ++
  "  assign o_stall_req_rs0 = u_cpu.u_cpu.stall_req_rs0;\n" ++
  "  assign o_redirect_or = u_cpu.u_cpu.redirect_or;\n" ++
  "  assign o_pipeline_flush = u_cpu.u_cpu.pipeline_flush;\n" ++
  "  assign o_dmem_stall_ext = u_cpu.u_cpu.dmem_stall_ext;\n" ++
  "  assign o_fetch_stall_ext = u_cpu.u_cpu.fetch_stall_ext;\n" ++
  "  assign o_fp_drain_mode = u_cpu.u_cpu.fp_drain_mode;\n" ++
  "  assign o_fp_stale_suppress = u_cpu.u_cpu.fp_stale_suppress;\n" ++
  "  assign o_fp_valid_out = u_cpu.u_cpu.fp_valid_out;\n" ++
  "  assign o_fp_enq_valid_gated = u_cpu.u_cpu.fp_enq_valid_gated;\n" ++
  "  assign o_fp_drain_hold = u_cpu.u_cpu.fp_drain_hold;\n" ++
  "  assign o_fallback_cdb_inject = u_cpu.u_cpu.fallback_cdb_inject;\n" ++
  "  assign o_all_cdb_inject = u_cpu.u_cpu.all_cdb_inject;\n" ++
  "  assign o_cdb_valid_fp_prf = u_cpu.u_cpu.cdb_valid_fp_prf;\n" ++
  "  assign o_d0_base_tmp = u_cpu.u_cpu.d0_base_tmp;\n" ++
  "  assign o_d0_base_pre = u_cpu.u_cpu.d0_base_pre;\n" ++
  "  assign o_rs_e0_valid = u_cpu.u_cpu.u_rs_fp.e0[0];\n" ++
  "  assign o_rs_e1_valid = u_cpu.u_cpu.u_rs_fp.e1[0];\n" ++
  "  assign o_rs_e0_ready = u_cpu.u_cpu.u_rs_fp.e0_ready;\n" ++
  "  assign o_rs_e1_ready = u_cpu.u_cpu.u_rs_fp.e1_ready;\n" ++
  "  assign o_lsu_sb_empty = u_cpu.u_cpu.lsu_sb_empty;\n" ++
  "  assign o_lsu_sb_deq_valid = u_cpu.u_cpu.lsu_sb_deq_valid;\n" ++
  "  assign o_commit_store_en = u_cpu.u_cpu.commit_store_en;\n" ++
  "  // Store-buffer state, packed.  Bits are documented by the extractor in\n" ++
  "  // the cosim main; the bitmap bytes are the enqueue/commit/dequeue state.\n" ++
  "  assign o_dbg_sb = {\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.committed_e7, u_cpu.u_cpu.u_lsu.u_store_buffer.committed_e6,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.committed_e5, u_cpu.u_cpu.u_lsu.u_store_buffer.committed_e4,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.committed_e3, u_cpu.u_cpu.u_lsu.u_store_buffer.committed_e2,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.committed_e1, u_cpu.u_cpu.u_lsu.u_store_buffer.committed_e0,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.valid_e7, u_cpu.u_cpu.u_lsu.u_store_buffer.valid_e6,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.valid_e5, u_cpu.u_cpu.u_lsu.u_store_buffer.valid_e4,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.valid_e3, u_cpu.u_cpu.u_lsu.u_store_buffer.valid_e2,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.valid_e1, u_cpu.u_cpu.u_lsu.u_store_buffer.valid_e0,\n" ++
  "    1'b0, u_cpu.u_cpu.sb_alloc_ctr,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.commit_ptr_,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.tail_ptr_,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.head_ptr_,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.count_,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.pending_commit,\n" ++
  "    u_cpu.u_cpu.csp_,\n" ++
  "    u_cpu.u_cpu.sb_dispatch_idx,\n" ++
  "    u_cpu.u_cpu.pipeline_flush,\n" ++
  "    u_cpu.u_cpu.sb_enq_dispatched,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.flush_pending,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.deq_valid,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.commit_target_valid,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.commit_en_gated,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.deq_fire,\n" ++
  "    u_cpu.u_cpu.u_lsu.u_store_buffer.enq_en,\n" ++
  "    u_cpu.u_cpu.commit_store_s1, u_cpu.u_cpu.commit_store_s0,\n" ++
  "    u_cpu.u_cpu.commit_en[1], u_cpu.u_cpu.commit_en[0],\n" ++
  "    u_cpu.u_cpu.rob_head_isStore[1], u_cpu.u_cpu.rob_head_isStore[0],\n" ++
  "    u_cpu.u_cpu.rob_head_idx_1, u_cpu.u_cpu.rob_head_idx_0\n" ++
  "  };\n" ++
  "  // CSR capture, packed: the address/phys/rd latches the serialize FSM takes\n" ++
  "  // when it detects a CSR instruction, plus the read data it publishes.\n" ++
  "  assign o_dbg_csr = {\n" ++
  "    u_cpu.u_cpu.csr_addr_e, u_cpu.u_cpu.csr_phcap_e, u_cpu.u_cpu.csr_rdcap_e,\n" ++
  "    u_cpu.u_cpu.csr_flag_reg, u_cpu.u_cpu.fence_i_start, u_cpu.u_cpu.csr_selected,\n" ++
  "    u_cpu.u_cpu.csr_detected, u_cpu.u_cpu.ser_slot_sel, u_cpu.u_cpu.csr_rename_en,\n" ++
  "    u_cpu.u_cpu.csr_drain_complete, u_cpu.u_cpu.fence_i_draining, u_cpu.u_cpu.useq_active,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e31, u_cpu.u_cpu.csr_cdb_dt_e30, u_cpu.u_cpu.csr_cdb_dt_e29,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e28, u_cpu.u_cpu.csr_cdb_dt_e27, u_cpu.u_cpu.csr_cdb_dt_e26,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e25, u_cpu.u_cpu.csr_cdb_dt_e24, u_cpu.u_cpu.csr_cdb_dt_e23,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e22, u_cpu.u_cpu.csr_cdb_dt_e21, u_cpu.u_cpu.csr_cdb_dt_e20,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e19, u_cpu.u_cpu.csr_cdb_dt_e18, u_cpu.u_cpu.csr_cdb_dt_e17,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e16, u_cpu.u_cpu.csr_cdb_dt_e15, u_cpu.u_cpu.csr_cdb_dt_e14,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e13, u_cpu.u_cpu.csr_cdb_dt_e12, u_cpu.u_cpu.csr_cdb_dt_e11,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e10, u_cpu.u_cpu.csr_cdb_dt_e9, u_cpu.u_cpu.csr_cdb_dt_e8,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e7, u_cpu.u_cpu.csr_cdb_dt_e6, u_cpu.u_cpu.csr_cdb_dt_e5,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e4, u_cpu.u_cpu.csr_cdb_dt_e3, u_cpu.u_cpu.csr_cdb_dt_e2,\n" ++
  "    u_cpu.u_cpu.csr_cdb_dt_e1, u_cpu.u_cpu.csr_cdb_dt_e0\n" ++
  "  };\n" ++
  "  assign o_dbg_atm = { u_cpu.u_cpu.atom_aw_addr, u_cpu.u_cpu.mem_addr_r };\n" ++
  "  assign o_dbg_atmf = { u_cpu.u_cpu.dmem_resp_data[31:0], u_cpu.u_cpu.dmem_req_addr };\n" ++
  "  assign o_dbg_ren = {\n" ++
  "    u_cpu.u_cpu.cdb_valid, u_cpu.u_cpu.cdb_tag_1, u_cpu.u_cpu.cdb_tag_0,\n" ++
  "    u_cpu.u_cpu.commit_en, u_cpu.u_cpu.int_retire_any_old,\n" ++
  "    u_cpu.u_cpu.retire_tag_bt_1, u_cpu.u_cpu.retire_tag_bt_0,\n" ++
  "    u_cpu.u_cpu.mem_dispatch_valid, u_cpu.u_cpu.mem_mux_src2_ready, u_cpu.u_cpu.mem_mux_rs2_phys,\n" ++
  "    u_cpu.u_cpu.rd_phys_1, u_cpu.u_cpu.rd_phys_0, u_cpu.u_cpu.dispatch_base_valid,\n" ++
  "    u_cpu.u_cpu.d1_has_rd_int, u_cpu.u_cpu.d0_has_rd_int,\n" ++
  "    u_cpu.u_cpu.d1_force_alloc, u_cpu.u_cpu.d0_force_alloc, 8'b0\n" ++
  "  };\n" ++
  "  assign o_dbg_ren2 = {\n" ++
  "    7'b0, u_cpu.u_cpu.fence_i_start, u_cpu.u_cpu.fallback_seq_start, u_cpu.u_cpu.csr_rename_en,\n" ++
  "    u_cpu.u_cpu.csr_phcap_e, u_cpu.u_cpu.csr_ophcap_e,\n" ++
  "    u_cpu.u_cpu.csr_cdb_inject, u_cpu.u_cpu.fallback_cdb_inject,\n" ++
  "    u_cpu.u_cpu.csr_commit_valid_0, u_cpu.u_cpu.csr_retire_hasPhysRd_0, u_cpu.u_cpu.csr_commit_hasPhysRd_0,\n" ++
  "    u_cpu.u_cpu.cmt_retag_mux_0, u_cpu.u_cpu.cmt_physRd_mux_0, u_cpu.u_cpu.cmt_archRd_mux_0,\n" ++
  "    u_cpu.u_cpu.dec1_rd, u_cpu.u_cpu.dec0_rd, 10'b0 };\n" ++
  "  assign o_dbg_cdbd = { u_cpu.u_cpu.cdb_data_1[31:0], u_cpu.u_cpu.cdb_data_0[31:0] };\n" ++
  "  assign o_dbg_atmf2 = {\n" ++
  "    10'b0, u_cpu.u_cpu.pipeline_flush_comb, u_cpu.u_cpu.atom_aw_clr,\n" ++
  "    u_cpu.u_cpu.atom_lr_resp, u_cpu.u_cpu.cross_size_stall, u_cpu.u_cpu.atom_sc_exec,\n" ++
  "    u_cpu.u_cpu.atom_load_ok, u_cpu.u_cpu.atom_disp_ok, u_cpu.u_cpu.lsu_sb_empty,\n" ++
  "    u_cpu.u_cpu.lsu_sb_deq_valid, u_cpu.u_cpu.mem_valid_r, u_cpu.u_cpu.is_load_r,\n" ++
  "    u_cpu.u_cpu.load_no_fwd, u_cpu.u_cpu.dmem_req_we, u_cpu.u_cpu.dmem_req_valid,\n" ++
  "    u_cpu.u_cpu.atom_aw_set, u_cpu.u_cpu.atom_aw_pending, u_cpu.u_cpu.atom_resp_live,\n" ++
  "    u_cpu.u_cpu.atom_amo_resp, u_cpu.u_cpu.atom_busy, u_cpu.u_cpu.dmem_load_pending,\n" ++
  "    u_cpu.u_cpu.dmem_resp_valid\n" ++
  "  };\n" ++
  "  assign o_dbg_amo = {\n" ++
  "    u_cpu.u_cpu.mem_mux_is_atomic, u_cpu.u_cpu.is_amo, u_cpu.u_cpu.is_sc, u_cpu.u_cpu.is_load,\n" ++
  "    u_cpu.u_cpu.rs_mem_dispatch_valid, u_cpu.u_cpu.sb_enq_ungated, u_cpu.u_cpu.mem_store_dispatch_en,\n" ++
  "    u_cpu.u_cpu.atom_disp_ok, u_cpu.u_cpu.atom_busy, u_cpu.u_cpu.atom_aw_pending,\n" ++
  "    u_cpu.u_cpu.lsu_sb_empty, u_cpu.u_cpu.dmem_load_pending, u_cpu.u_cpu.pipe_valid_hold,\n" ++
  "    u_cpu.u_cpu.mem_dispatch_en_any, u_cpu.u_cpu.is_load_r, u_cpu.u_cpu.mem_valid_r,\n" ++
  "    u_cpu.u_cpu.dmem_req_valid, u_cpu.u_cpu.dmem_req_we, u_cpu.u_cpu.lsu_valid,\n" ++
  "    u_cpu.u_cpu.lsu_sb_deq_valid, u_cpu.u_cpu.pipeline_flush_comb, u_cpu.u_cpu.fence_i_draining,\n" ++
  "    u_cpu.u_cpu.suppress_all, u_cpu.u_cpu.hw_draining_reg,\n" ++
  "    8'b0\n" ++
  "  };\n" ++
  "  assign o_hw_draining_reg = u_cpu.u_cpu.hw_draining_reg;\n" ++
  "  assign o_fence_start_delayed = u_cpu.u_cpu.fence_start_delayed;\n" ++
  "  assign o_lsu_sb_full = u_cpu.u_cpu.lsu_sb_full;\n" ++
  "  assign o_lsu_sb_flush_pending = u_cpu.u_cpu.lsu_sb_flush_pending;\n" ++
  "  assign o_fi_start_nocsr = u_cpu.u_cpu.fi_start_nocsr;\n" ++
  "  assign o_fence_i_draining = u_cpu.u_cpu.fence_i_draining;\n" ++
  "  assign o_d0_needs_sb = u_cpu.u_cpu.d0_needs_sb;\n" ++
  "  assign o_hw_suppress = u_cpu.u_cpu.hw_suppress;\n" ++
  "  assign o_useq_active = u_cpu.u_cpu.useq_active;\n" ++
  "  assign o_fallback_active = u_cpu.u_cpu.fallback_active;\n" ++
  "  assign o_stall_req_im = u_cpu.u_cpu.stall_req_im;\n" ++
  "  assign o_stall_req_bm = u_cpu.u_cpu.stall_req_bm;\n" ++
  "  assign o_fp_stall_req_0 = u_cpu.u_cpu.fp_stall_req_0;\n" ++
  "  assign o_sb_stall_req_0 = u_cpu.u_cpu.sb_stall_req_0;\n" ++
  "  assign o_suppress_pre = u_cpu.u_cpu.suppress_pre;\n" ++
  "  assign o_dmem_we         = u_cpu.u_cpu.dmem_req_we;\n" ++
  "  assign o_dmem_req_v      = u_cpu.u_cpu.dmem_req_valid;\n" ++
  "  assign o_req_addr        = u_cpu.u_cpu.dmem_req_addr;\n" ++
  "  assign o_req_data        = u_cpu.u_cpu.dmem_req_data;\n" ++
  "  assign o_req_size        = u_cpu.u_cpu.dmem_req_size;\n" ++
  "  assign o_sb_deq_v        = u_cpu.u_cpu.lsu_sb_deq_valid;\n" ++
  "  assign o_sb_empty        = u_cpu.u_cpu.lsu_sb_empty;\n" ++
  "  assign o_sb_full         = u_cpu.u_cpu.lsu_sb_full;\n" ++
  "  assign o_load_pending    = u_cpu.u_cpu.dmem_load_pending;\n" ++
  "  assign o_aw_pend         = u_cpu.u_cpu.atom_aw_pending;\n" ++
  "  assign o_sb_cnt          = u_cpu.u_cpu.lsu_sb_deq_bits[31:0];\n" ++
  "  assign o_load_addr       = u_cpu.u_cpu.mem_addr_r;\n" ++
  "  assign o_load_size       = u_cpu.u_cpu.mem_size_r;\n" ++
  "  assign o_tohost          = test_code;\n" ++
  "  assign o_rvvi_valid_0    = rvvi_validS0;\n" ++
  "  assign o_rvvi_valid_1    = rvvi_validS1;\n" ++
  "  assign o_rvvi_trap_0     = rvvi_trapS0;\n" ++
  "  assign o_rvvi_trap_1     = rvvi_trapS1;\n" ++
  "  assign o_rvvi_pc_rdata_0 = rvvi_pc_0;\n" ++
  "  assign o_rvvi_pc_rdata_1 = rvvi_pc_1;\n" ++
  "  assign o_rvvi_insn_0     = rvvi_insn_0;\n" ++
  "  assign o_rvvi_insn_1     = rvvi_insn_1;\n" ++
  "  assign o_rvvi_rd_0       = rvvi_rd_0;\n" ++
  "  assign o_rvvi_rd_1       = rvvi_rd_1;\n" ++
  "  assign o_rvvi_rd_valid_0 = rvvi_rd_validS0;\n" ++
  "  assign o_rvvi_rd_valid_1 = rvvi_rd_validS1;\n" ++
  "  assign o_rvvi_rd_data_0  = rvvi_rdd_0;\n" ++
  "  assign o_rvvi_rd_data_1  = rvvi_rdd_1;\n" ++
  "  assign o_rvvi_is_fp_0    = rvvi_is_fpS0;\n" ++
  "  assign o_rvvi_is_fp_1    = rvvi_is_fpS1;\n" ++
  "  assign o_rvvi_fflags_0   = rvvi_fflags;\n" ++
  "  assign o_rvvi_fflags_slot1   = rvvi_fflags_slot1;\n" ++
  "  assign o_rvvi_fp_rd_data   = rvvi_fprd;\n" ++
  "  assign o_rvvi_fp_rd_data_slot1 = rvvi_fprd_slot1;\n\n" ++
  "endmodule\n"

/-! ## Verilator sim_main.cpp Generator -/

/-- Generate sim_main.cpp for Verilator simulation, templated on testbench config. -/
def toSimMainCpp (cfg : TestbenchConfig) : String :=
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let vType := s!"V{tbName}"
  let isCached := cfg.cacheLineMemPort.isSome
  let lb := "{"
  let rb := "}"

  "//==============================================================================\n" ++
  s!"// sim_main_{tbName}.cpp - Auto-generated Verilator testbench driver\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstring>\n" ++
  "#include <memory>\n" ++
  "#include <elf.h>\n\n" ++
  "static struct _StdoutUnbuffer " ++ lb ++ "\n" ++
  "    _StdoutUnbuffer() " ++ lb ++ " setvbuf(stdout, nullptr, _IONBF, 0); " ++ rb ++ "\n" ++
  rb ++ " _stdout_unbuffer;\n\n" ++
  s!"#include \"{vType}.h\"\n" ++
  "#include \"verilated.h\"\n" ++
  "#include \"svdpi.h\"\n\n" ++
  "#if VM_TRACE\n" ++
  "#include \"verilated_fst_c.h\"\n" ++
  "#include <string>\n" ++
  "#endif\n\n" ++
  "#if VM_COVERAGE\n" ++
  "#include \"verilated_cov.h\"\n" ++
  "#include <filesystem>\n" ++
  "#include <string>\n" ++
  "#endif\n\n" ++
  "extern \"C\" void dpi_mem_write(unsigned int word_addr, unsigned int data);\n" ++
  "extern \"C\" void dpi_set_tohost_addr(unsigned int addr);\n" ++
  (if cfg.putcharAddr.isSome then
    "extern \"C\" void dpi_set_putchar_addr(unsigned int addr);\n"
   else "") ++
  "static FILE* g_uart_tx_file = nullptr;\n" ++
  "extern \"C\" void dpi_uart_tx_byte(char data) " ++ lb ++ "\n" ++
  "    if (g_uart_tx_file) " ++ lb ++ "\n" ++
  "        fputc(data, g_uart_tx_file);\n" ++
  "        fflush(g_uart_tx_file);\n" ++
  "    " ++ rb ++ "\n" ++
  rb ++ "\n\n" ++
  "static const uint32_t DEFAULT_TIMEOUT = " ++ toString cfg.timeoutCycles ++ ";\n\n" ++

  "static const char* get_plusarg(int argc, char** argv, const char* name) " ++ lb ++ "\n" ++
  "    size_t len = strlen(name);\n" ++
  "    for (int i = 1; i < argc; i++)\n" ++
  "        if (strncmp(argv[i], name, len) == 0 && argv[i][len] == '=')\n" ++
  "            return argv[i] + len + 1;\n" ++
  "    return nullptr;\n" ++
  rb ++ "\n\n" ++
  "static bool has_plusarg(int argc, char** argv, const char* name) " ++ lb ++ "\n" ++
  "    for (int i = 1; i < argc; i++)\n" ++
  "        if (strcmp(argv[i], name) == 0) return true;\n" ++
  "    return false;\n" ++
  rb ++ "\n\n" ++

  -- ELF symbol lookup
  "static int64_t elf_lookup_symbol(const char* path, const char* sym_name) " ++ lb ++ "\n" ++
  "    FILE* f = fopen(path, \"rb\");\n" ++
  "    if (!f) return -1;\n" ++
  "    unsigned char ident[EI_NIDENT];\n" ++
  "    if (fread(ident, 1, EI_NIDENT, f) != EI_NIDENT) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "    fseek(f, 0, SEEK_SET);\n" ++
  "    if (ident[EI_CLASS] == ELFCLASS64) " ++ lb ++ "\n" ++
  "        Elf64_Ehdr ehdr;\n" ++
  "        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "        for (int i = 0; i < ehdr.e_shnum; i++) " ++ lb ++ "\n" ++
  "            Elf64_Shdr shdr;\n" ++
  "            fseek(f, ehdr.e_shoff + i * ehdr.e_shentsize, SEEK_SET);\n" ++
  "            if (fread(&shdr, sizeof(shdr), 1, f) != 1) continue;\n" ++
  "            if (shdr.sh_type != SHT_SYMTAB) continue;\n" ++
  "            Elf64_Shdr strhdr;\n" ++
  "            fseek(f, ehdr.e_shoff + shdr.sh_link * ehdr.e_shentsize, SEEK_SET);\n" ++
  "            if (fread(&strhdr, sizeof(strhdr), 1, f) != 1) continue;\n" ++
  "            auto* strtab = new char[strhdr.sh_size];\n" ++
  "            fseek(f, strhdr.sh_offset, SEEK_SET);\n" ++
  "            if (fread(strtab, 1, strhdr.sh_size, f) != strhdr.sh_size) " ++ lb ++ " delete[] strtab; continue; " ++ rb ++ "\n" ++
  "            int nsyms = shdr.sh_size / shdr.sh_entsize;\n" ++
  "            for (int j = 0; j < nsyms; j++) " ++ lb ++ "\n" ++
  "                Elf64_Sym sym;\n" ++
  "                fseek(f, shdr.sh_offset + j * shdr.sh_entsize, SEEK_SET);\n" ++
  "                if (fread(&sym, sizeof(sym), 1, f) != 1) continue;\n" ++
  "                if (sym.st_name < strhdr.sh_size && strcmp(strtab + sym.st_name, sym_name) == 0) " ++ lb ++ "\n" ++
  "                    delete[] strtab; fclose(f); return (int64_t)sym.st_value;\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n" ++
  "            delete[] strtab;\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ " else " ++ lb ++ "\n" ++
  "        Elf32_Ehdr ehdr;\n" ++
  "        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "        for (int i = 0; i < ehdr.e_shnum; i++) " ++ lb ++ "\n" ++
  "            Elf32_Shdr shdr;\n" ++
  "            fseek(f, ehdr.e_shoff + i * ehdr.e_shentsize, SEEK_SET);\n" ++
  "            if (fread(&shdr, sizeof(shdr), 1, f) != 1) continue;\n" ++
  "            if (shdr.sh_type != SHT_SYMTAB) continue;\n" ++
  "            Elf32_Shdr strhdr;\n" ++
  "            fseek(f, ehdr.e_shoff + shdr.sh_link * ehdr.e_shentsize, SEEK_SET);\n" ++
  "            if (fread(&strhdr, sizeof(strhdr), 1, f) != 1) continue;\n" ++
  "            auto* strtab = new char[strhdr.sh_size];\n" ++
  "            fseek(f, strhdr.sh_offset, SEEK_SET);\n" ++
  "            if (fread(strtab, 1, strhdr.sh_size, f) != strhdr.sh_size) " ++ lb ++ " delete[] strtab; continue; " ++ rb ++ "\n" ++
  "            int nsyms = shdr.sh_size / shdr.sh_entsize;\n" ++
  "            for (int j = 0; j < nsyms; j++) " ++ lb ++ "\n" ++
  "                Elf32_Sym sym;\n" ++
  "                fseek(f, shdr.sh_offset + j * shdr.sh_entsize, SEEK_SET);\n" ++
  "                if (fread(&sym, sizeof(sym), 1, f) != 1) continue;\n" ++
  "                if (sym.st_name < strhdr.sh_size && strcmp(strtab + sym.st_name, sym_name) == 0) " ++ lb ++ "\n" ++
  "                    delete[] strtab; fclose(f); return (int64_t)sym.st_value;\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n" ++
  "            delete[] strtab;\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ "\n" ++
  "    fclose(f);\n" ++
  "    return -1;\n" ++
  rb ++ "\n\n" ++

  -- ELF loader
  "static int load_elf(const char* path) " ++ lb ++ "\n" ++
  "    FILE* f = fopen(path, \"rb\");\n" ++
  "    if (!f) " ++ lb ++ " fprintf(stderr, \"ERROR: Cannot open ELF: %s\\n\", path); return -1; " ++ rb ++ "\n" ++
  "    unsigned char ident[EI_NIDENT];\n" ++
  "    if (fread(ident, 1, EI_NIDENT, f) != EI_NIDENT) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "    if (memcmp(ident, ELFMAG, SELFMAG) != 0) " ++ lb ++ "\n" ++
  "        fprintf(stderr, \"ERROR: Not an ELF file\\n\"); fclose(f); return -1;\n" ++
  "    " ++ rb ++ "\n" ++
  "    fseek(f, 0, SEEK_SET);\n" ++
  "    uint32_t total = 0;\n" ++
  "    if (ident[EI_CLASS] == ELFCLASS64) " ++ lb ++ "\n" ++
  "        Elf64_Ehdr ehdr;\n" ++
  "        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "        for (int i = 0; i < ehdr.e_phnum; i++) " ++ lb ++ "\n" ++
  "            Elf64_Phdr phdr;\n" ++
  "            fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);\n" ++
  "            if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;\n" ++
  "            if (phdr.p_type != PT_LOAD || phdr.p_memsz == 0) continue;\n" ++
  "            for (uint64_t off = 0; off < phdr.p_memsz; off += 4)\n" ++
  "                dpi_mem_write((phdr.p_paddr + off) / 4, 0);\n" ++
  "            if (phdr.p_filesz > 0) " ++ lb ++ "\n" ++
  "                fseek(f, phdr.p_offset, SEEK_SET);\n" ++
  "                uint64_t words = (phdr.p_filesz + 3) / 4;\n" ++
  "                for (uint64_t w = 0; w < words; w++) " ++ lb ++ "\n" ++
  "                    uint32_t word = 0;\n" ++
  "                    uint64_t rem = phdr.p_filesz - w * 4;\n" ++
  "                    (void)fread(&word, 1, rem < 4 ? rem : 4, f);\n" ++
  "                    dpi_mem_write((phdr.p_paddr / 4) + w, word);\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n" ++
  "            printf(\"  PT_LOAD: paddr=0x%016lx filesz=%lu memsz=%lu\\n\", phdr.p_paddr, phdr.p_filesz, phdr.p_memsz);\n" ++
  "            total += phdr.p_memsz;\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ " else " ++ lb ++ "\n" ++
  "        Elf32_Ehdr ehdr;\n" ++
  "        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "        for (int i = 0; i < ehdr.e_phnum; i++) " ++ lb ++ "\n" ++
  "            Elf32_Phdr phdr;\n" ++
  "            fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);\n" ++
  "            if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;\n" ++
  "            if (phdr.p_type != PT_LOAD || phdr.p_memsz == 0) continue;\n" ++
  "            for (uint32_t off = 0; off < phdr.p_memsz; off += 4)\n" ++
  "                dpi_mem_write((phdr.p_paddr + off) / 4, 0);\n" ++
  "            if (phdr.p_filesz > 0) " ++ lb ++ "\n" ++
  "                fseek(f, phdr.p_offset, SEEK_SET);\n" ++
  "                uint32_t words = (phdr.p_filesz + 3) / 4;\n" ++
  "                for (uint32_t w = 0; w < words; w++) " ++ lb ++ "\n" ++
  "                    uint32_t word = 0;\n" ++
  "                    uint32_t rem = phdr.p_filesz - w * 4;\n" ++
  "                    (void)fread(&word, 1, rem < 4 ? rem : 4, f);\n" ++
  "                    dpi_mem_write((phdr.p_paddr / 4) + w, word);\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n" ++
  "            printf(\"  PT_LOAD: paddr=0x%08x filesz=%u memsz=%u\\n\", phdr.p_paddr, phdr.p_filesz, phdr.p_memsz);\n" ++
  "            total += phdr.p_memsz;\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ "\n" ++
  "    fclose(f);\n" ++
  "    printf(\"Loaded ELF %s (%u bytes)\\n\", path, total);\n" ++
  "    return (int)total;\n" ++
  rb ++ "\n\n" ++

  s!"int main(int argc, char** argv) {lb}\n" ++
  "    Verilated::commandArgs(argc, argv);\n" ++
  s!"    auto dut = std::make_unique<{vType}>();\n\n" ++
  "    const char* elf_path = get_plusarg(argc, argv, \"+elf\");\n" ++
  "    const char* timeout_str = get_plusarg(argc, argv, \"+timeout\");\n" ++
  "    const char* uart_log_path = get_plusarg(argc, argv, \"+uart_tx_log\");\n" ++
  "    if (uart_log_path) g_uart_tx_file = fopen(uart_log_path, \"wb\");\n" ++
  "    bool do_trace = has_plusarg(argc, argv, \"+trace\");\n" ++
  "    bool verbose = has_plusarg(argc, argv, \"+verbose\");\n" ++
  "    bool dump_rtl = get_plusarg(argc, argv, \"+dump_rtl\") != nullptr;\n" ++
  "    uint32_t timeout = timeout_str ? atoi(timeout_str) : DEFAULT_TIMEOUT;\n\n" ++
  "#if VM_TRACE\n" ++
  "    VerilatedFstC* trace = nullptr;\n" ++
  "    if (do_trace) " ++ lb ++ "\n" ++
  "        Verilated::traceEverOn(true);\n" ++
  "        trace = new VerilatedFstC;\n" ++
  "        dut->trace(trace, 99);\n" ++
  "        // bazel run starts in the runfiles tree: write where the user ran it.\n" ++
  "        const char* run_dir = getenv(\"BUILD_WORKING_DIRECTORY\");\n" ++
  s!"        std::string fst_path = std::string(run_dir ? run_dir : \".\") + \"/{tbName}.fst\";\n" ++
  "        trace->open(fst_path.c_str());\n" ++
  "        fprintf(stderr, \"trace: %s\\n\", fst_path.c_str());\n" ++
  "    " ++ rb ++ "\n" ++
  "#else\n" ++
  "    (void)do_trace;\n" ++
  "#endif\n\n" ++
  "    if (!elf_path) " ++ lb ++ "\n" ++
  "        fprintf(stderr, \"ERROR: No ELF file. Use +elf=path\\n\");\n" ++
  "        return 1;\n" ++
  "    " ++ rb ++ "\n\n" ++
  s!"    svSetScope(svGetScopeFromName(\"TOP.{tbName}\"));\n" ++
  "    if (load_elf(elf_path) < 0) return 1;\n\n" ++
  "    // Reset — must happen BEFORE DPI addr overrides so that initial blocks\n" ++
  "    // (which set default TOHOST_ADDR/PUTCHAR_ADDR) run first during eval().\n" ++
  "    dut->rst_n = 0; dut->clk = 0;\n" ++
  "    for (int i = 0; i < 10; i++) " ++ lb ++ "\n" ++
  "        dut->clk = !dut->clk; dut->eval();\n" ++
  "#if VM_TRACE\n" ++
  "        if (trace) trace->dump(i);\n" ++
  "#endif\n" ++
  "    " ++ rb ++ "\n" ++
  "    dut->rst_n = 1;\n\n" ++
  "    // Override HTIF/putchar addresses from ELF symbols AFTER reset,\n" ++
  "    // so initial blocks don't overwrite our values.\n" ++
  "    int64_t tohost_sym = elf_lookup_symbol(elf_path, \"tohost\");\n" ++
  "    if (tohost_sym >= 0) " ++ lb ++ "\n" ++
  "        printf(\"ELF symbol: tohost = 0x%08x\\n\", (uint32_t)tohost_sym);\n" ++
  "        dpi_set_tohost_addr((uint32_t)tohost_sym);\n" ++
  "    " ++ rb ++ "\n" ++
  (if cfg.putcharAddr.isSome then
    "    int64_t putchar_sym = elf_lookup_symbol(elf_path, \"putchar_addr\");\n" ++
    "    if (putchar_sym >= 0) " ++ lb ++ "\n" ++
    "        printf(\"ELF symbol: putchar_addr = 0x%08x\\n\", (uint32_t)putchar_sym);\n" ++
    "        dpi_set_putchar_addr((uint32_t)putchar_sym);\n" ++
    "    " ++ rb ++ "\n"
   else "") ++
  "\n" ++
  "#if VM_TRACE\n" ++
  "    uint64_t sim_time = 10;\n" ++
  "#endif\n" ++
  "    uint32_t cycle = 0, retired = 0;\n" ++
  "    bool done = false;\n\n" ++
  "    printf(\"Harness built %s %s\\n\", __DATE__, __TIME__);\n" ++
  "    printf(\"Simulation started (timeout=%u cycles)\\n\", timeout);\n" ++
  "    printf(\"─────────────────────────────────────────────\\n\");\n\n" ++
  "    while (!done && cycle < timeout && !Verilated::gotFinish()) " ++ lb ++ "\n" ++
  "        dut->clk = 1; dut->eval();\n" ++
  "#if VM_TRACE\n" ++
  "        if (trace) trace->dump(sim_time++);\n" ++
  "#endif\n\n" ++
  "        // Dual-retire RVVI (W=2)\n" ++
  "        if (dut->o_rvvi_valid_0) " ++ lb ++ "\n" ++
  "            retired++;\n" ++
  "            if (dump_rtl)\n" ++
  "                printf(\"RET pc=%016lx insn=%08x rd=%u rdv=%016lx frd=%u frdv=%016lx fl=%02x\\n\",\n" ++
  "                    (unsigned long)dut->o_rvvi_pc_rdata_0, dut->o_rvvi_insn_0,\n" ++
  "                    dut->o_rvvi_is_fp_0 ? 0u : dut->o_rvvi_rd_0,\n" ++
  "                    (dut->o_rvvi_is_fp_0 || dut->o_rvvi_rd_0 == 0u) ? 0ul : (unsigned long)dut->o_rvvi_rd_data_0,\n" ++
  "                    dut->o_rvvi_is_fp_0 ? dut->o_rvvi_rd_0 : 0u,\n" ++
  "                    dut->o_rvvi_is_fp_0 ? (unsigned long)dut->o_rvvi_fp_rd_data : 0ul,\n" ++
  "                    (unsigned)dut->o_rvvi_fflags_0);\n" ++
  "            if (verbose)\n" ++
  "                printf(\"  RET0[cy%u #%u] PC=0x%08x insn=0x%08x rd=x%u(%d) data=0x%016lx\\n\",\n" ++
  "                    cycle, retired, dut->o_rvvi_pc_rdata_0, dut->o_rvvi_insn_0,\n" ++
  "                    dut->o_rvvi_rd_0, (int)dut->o_rvvi_rd_valid_0, (unsigned long)dut->o_rvvi_rd_data_0);\n" ++
  "        " ++ rb ++ "\n" ++
  "        if (dut->o_rvvi_valid_1) " ++ lb ++ "\n" ++
  "            retired++;\n" ++
  "            if (dump_rtl)\n" ++
  "                printf(\"RET pc=%016lx insn=%08x rd=%u rdv=%016lx frd=%u frdv=%016lx fl=%02x\\n\",\n" ++
  "                    (unsigned long)dut->o_rvvi_pc_rdata_1, dut->o_rvvi_insn_1,\n" ++
  "                    dut->o_rvvi_is_fp_1 ? 0u : dut->o_rvvi_rd_1,\n" ++
  "                    (dut->o_rvvi_is_fp_1 || dut->o_rvvi_rd_1 == 0u) ? 0ul : (unsigned long)dut->o_rvvi_rd_data_1,\n" ++
  "                    dut->o_rvvi_is_fp_1 ? dut->o_rvvi_rd_1 : 0u,\n" ++
  "                    dut->o_rvvi_is_fp_1 ? (unsigned long)dut->o_rvvi_fp_rd_data_slot1 : 0ul,\n" ++
  "                    (unsigned)dut->o_rvvi_fflags_slot1);\n" ++
  "            if (verbose)\n" ++
  "                printf(\"  RET1[cy%u #%u] PC=0x%08x insn=0x%08x rd=x%u(%d) data=0x%016lx\\n\",\n" ++
  "                    cycle, retired, dut->o_rvvi_pc_rdata_1, dut->o_rvvi_insn_1,\n" ++
  "                    dut->o_rvvi_rd_1, (int)dut->o_rvvi_rd_valid_1, (unsigned long)dut->o_rvvi_rd_data_1);\n" ++
  "        " ++ rb ++ "\n\n" ++
  (if !isCached then
    "        if (verbose && dut->o_dmem_req_valid)\n" ++
    "            printf(\"  %s cy%u addr=0x%08x data=0x%08x\\n\",\n" ++
    "                dut->o_dmem_req_we ? \"STORE\" : \"LOAD \",\n" ++
    "                cycle, dut->o_dmem_req_addr, dut->o_dmem_req_data);\n\n"
   else
    "        if (verbose && dut->o_mem_req_valid)\n" ++
    "            printf(\"  %s cy%u addr=0x%08x\\n\",\n" ++
    "                dut->o_mem_req_we ? \"WB   \" : \"FETCH\", cycle, dut->o_mem_req_addr);\n\n") ++
  "        if (dut->o_test_done) " ++ lb ++ "\n" ++
  "            done = true;\n" ++
  "            printf(\"\\n══════ TEST %s ══════\\n\", dut->o_test_pass ? \"PASS\" : \"FAIL\");\n" ++
  "            if (!dut->o_test_pass) printf(\"  test_num:  %u\\n\", dut->o_test_code >> 1);\n" ++
  "            printf(\"  Cycle:     %u\\n\", cycle);\n" ++
  "            printf(\"  Retired:   %u\\n\", retired);\n" ++
  "            printf(\"  IPC:       %.3f\\n\", cycle > 0 ? (double)retired / cycle : 0.0);\n" ++
  "            printf(\"  tohost:    0x%08x\\n\", dut->o_test_code);\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        dut->clk = 0; dut->eval();\n" ++
  "#if VM_TRACE\n" ++
  "        if (trace) trace->dump(sim_time++);\n" ++
  "#endif\n" ++
  "        cycle++;\n" ++
  "        if (verbose && cycle % 10000 == 0)\n" ++
  "            printf(\"  [%u cycles]\\n\", cycle);\n" ++
  "    " ++ rb ++ "\n\n" ++
  "    if (!done) " ++ lb ++ "\n" ++
  "        printf(\"\\n══════ TIMEOUT ══════\\n\");\n" ++
  "        printf(\"  Cycle: %u  rob_empty: %d\\n\", cycle, dut->o_rob_empty);\n" ++
  "    " ++ rb ++ "\n" ++
  "    printf(\"─────────────────────────────────────────────\\n\");\n" ++
  "    printf(\"Total cycles: %u\\n\", cycle);\n" ++
  "    printf(\"Total retired: %u\\n\", retired);\n" ++
  "    printf(\"IPC: %.3f\\n\", cycle > 0 ? (double)retired / cycle : 0.0);\n\n" ++
  "#if VM_TRACE\n" ++
  "    if (trace) " ++ lb ++ " trace->close(); delete trace; " ++ rb ++ "\n" ++
  "#endif\n" ++
  "#if VM_COVERAGE\n" ++
  "    const char* cov_file = get_plusarg(argc, argv, \"+cov_file\");\n" ++
  "    if (!cov_file) cov_file = \"output/coverage/coverage.dat\";\n" ++
  "    std::string cov_path(cov_file);\n" ++
  "    auto slash_pos = cov_path.find_last_of(\"/\\\\\");\n" ++
  "    if (slash_pos != std::string::npos) " ++ lb ++ "\n" ++
  "        std::filesystem::create_directories(cov_path.substr(0, slash_pos));\n" ++
  "    " ++ rb ++ "\n" ++
  "    VerilatedCov::write(cov_file);\n" ++
  "#endif\n" ++
  "    if (g_uart_tx_file) { fclose(g_uart_tx_file); g_uart_tx_file = nullptr; }\n" ++
  "    dut->final();\n" ++
  "    return done && dut->o_test_pass ? 0 : 1;\n" ++
  rb ++ "\n"

/-! ## LeanSim Generator (replaces hand-written cppsim_oracle) -/

/-- Generate lean_sim header for a given testbench config. -/
def toLeanSimH (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let isCached := cfg.cacheLineMemPort.isSome
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)
  let lb := "{"
  let rb := "}"

  -- Build signal member declarations from circuit ports
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)
  let busWireNames : List String :=
    groups.flatMap (fun sg => sg.wires.map Wire.name)

  -- All ports minus reset
  let allPorts := c.inputs ++ c.outputs
  let portList := allPorts.filter fun w => w.name != resetName

  -- Scalar signals (not in any bus, not clock/constant)
  let isSpecial (name : String) : Bool :=
    (clockWires.any fun cw => cw.name == name) ||
    name == resetName ||
    cfg.constantPorts.any (fun (cn, _) => cn == name)

  let scalarPorts := portList.filter fun w =>
    !busWireNames.contains w.name && !isSpecial w.name
  let scalarDecls := String.intercalate "\n" (
    scalarPorts.map fun w => s!"    bool {w.name}_ = false;")

  -- Bus signal declarations
  let busDecls := String.intercalate "\n" (
    groups.map fun sg => s!"    bool {sg.name}_[{sg.width}] = {lb}{rb};")

  -- Bus pointer array declarations (for read_bus/write_bus)
  let busPtrDecls := String.intercalate "\n" (
    groups.map fun sg => s!"    bool* {sg.name}_sigs_[{sg.width}];")

  "// Auto-generated Lean gate-level simulation. DO NOT EDIT.\n" ++
  s!"// Generated from circuit: {c.name}\n" ++
  s!"#pragma once\n\n" ++
  "#include <cstdint>\n" ++
  "#include <string>\n\n" ++
  s!"#include \"cpu_setup_{c.name}.h\"\n" ++
  "#include \"elf_loader.h\"\n\n" ++
  s!"struct LeanSimStepResult {lb}\n" ++
  "    uint32_t pc;\n" ++
  "    uint32_t insn;\n" ++
  "    uint32_t rd;\n" ++
  "    uint32_t rd_data;\n" ++
  "    bool     rd_valid;\n" ++
  "    uint32_t frd;\n" ++
  "    uint32_t frd_data;\n" ++
  "    bool     frd_valid;\n" ++
  "    uint32_t fflags;\n" ++
  "    bool     done;\n" ++
  "    uint32_t tohost;\n" ++
  s!"{rb};\n\n" ++
  s!"class LeanSim {lb}\n" ++
  "public:\n" ++
  "    explicit LeanSim(const std::string& elf_path);\n" ++
  "    ~LeanSim();\n" ++
  "    LeanSimStepResult step();\n" ++
  "    uint32_t cycle() const { return cycle_; }\n\n" ++
  "private:\n" ++
  "    static constexpr uint32_t MEM_SIZE_WORDS = " ++ toString cfg.memSizeWords ++ ";\n" ++
  "    uint32_t mem_[MEM_SIZE_WORDS] = " ++ lb ++ rb ++ ";\n" ++
  "    CpuCtx* ctx_ = nullptr;\n\n" ++
  "    // Special signals\n" ++
  "    bool clock_sig_ = false;\n" ++
  "    bool reset_sig_ = false;\n" ++
  (String.intercalate "\n" (
    cfg.constantPorts.map fun (name, val) =>
      s!"    bool {name}_sig_ = {if val then "true" else "false"};")) ++ "\n\n" ++
  "    // Scalar signals\n" ++
  scalarDecls ++ "\n\n" ++
  "    // Bus signals\n" ++
  busDecls ++ "\n\n" ++
  "    // Bus pointer arrays\n" ++
  busPtrDecls ++ "\n\n" ++
  (if !isCached then
    "    // Dmem state\n" ++
    "    bool dmem_pending_ = false;\n" ++
    "    uint32_t dmem_read_data_ = 0;\n"
   else
    "    // Cache-line memory state\n" ++
    "    bool mem_pending_ = false;\n" ++
    "    uint32_t mem_read_line_[8] = " ++ lb ++ rb ++ ";\n") ++
  "    bool test_done_ = false;\n" ++
  "    uint32_t test_data_ = 0;\n" ++
  "    uint32_t cycle_ = 0;\n" ++
  "    static constexpr uint32_t MAX_CYCLES = 200000;\n\n" ++
  "    uint32_t read_bus(bool** sigs, int bits);\n" ++
  "    void write_bus(bool** sigs, uint32_t val, int bits);\n" ++
  (if !isCached then
    "    void imem_update();\n" ++
    "    void dmem_tick(bool req_valid, bool req_we, uint32_t addr, uint32_t data, uint32_t size);\n"
   else
    "    void mem_tick(bool req_valid, bool req_we, uint32_t addr, uint32_t* data_line);\n") ++
  "    void settle();\n" ++
  s!"{rb};\n"

/-- Generate lean_sim cpp for a given testbench config. -/
def toLeanSimCpp (cfg : TestbenchConfig) : String :=
  let c := cfg.circuit
  let isCached := cfg.cacheLineMemPort.isSome
  let clockWires := findClockWires c
  let resetWires := findResetWires c
  let resetName := if resetWires.isEmpty then "reset" else Wire.name (List.head! resetWires)
  let lb := "{"
  let rb := "}"

  -- Build port list (same as toCpuSetupCpp: exclude reset only)
  let allPorts := c.inputs ++ c.outputs
  let portList := allPorts.filter fun w =>
    w.name != resetName

  -- Detect signal groups to distinguish bus wires from scalar wires
  let groups := SystemVerilog.autoDetectSignalGroups (c.inputs ++ c.outputs)
  let busWireMap : List (String × String × Nat) :=
    groups.flatMap fun sg =>
      sg.wires.enum.map fun ⟨i, w⟩ => (w.name, sg.name, i)

  -- RVVI retire sideband names differ per CPU: the uncached CPU exposes a
  -- single `rvvi_valid` + `rvvi_pc_rdata`/`rvvi_rd_data`/`rvvi_frd_data` and an
  -- `fflags_acc` sideband; the cached (CachedCPU) top uses dual-slot
  -- `rvvi_validS0/S1` + `rvvi_pc_0`/`rvvi_rdd_0` and no frd/fflags ports.
  let groupExists (n : String) : Bool := groups.any fun sg => sg.name == n
  let portExists (n : String) : Bool :=
    (c.inputs ++ c.outputs).any fun w => w.name == n
  let busOf (candidates : List String) (fallback : String) : String :=
    match candidates.find? groupExists with
    | some n => n
    | none => fallback
  let rvviValidName := if portExists "rvvi_valid" then "rvvi_valid" else "rvvi_validS0"
  let rvviRdValidName := if portExists "rvvi_rd_valid" then "rvvi_rd_valid" else "rvvi_rd_validS0"
  let rvviPcBus := busOf ["rvvi_pc_rdata", "rvvi_pc_0"] "rvvi_pc_rdata"
  let rvviInsnBus := busOf ["rvvi_insn", "rvvi_insn_0"] "rvvi_insn"
  let rvviRdBus := busOf ["rvvi_rd", "rvvi_rd_0"] "rvvi_rd"
  let rvviRdDataBus := busOf ["rvvi_rd_data", "rvvi_rdd_0"] "rvvi_rd_data"
  let rvviFrdBus := busOf ["rvvi_frd", "rvvi_frd_0"] "rvvi_frd"
  let rvviFrdDataBus := busOf ["rvvi_frd_data", "rvvi_frdd_0"] "rvvi_frd_data"
  let hasFFlags := portExists "fflags_acc"

  -- Generate the port pointer array entries with correct signal variable names
  let portPtrEntries := String.intercalate ",\n" (
    portList.map fun w =>
      let wireName := w.name
      -- Clock -> &clock_sig_
      if (clockWires.any fun cw => cw.name == wireName) then
        "        &clock_sig_"
      -- Constants -> &{name}_sig_
      else if cfg.constantPorts.any (fun (cn, _) => cn == wireName) then
        s!"        &{wireName}_sig_"
      -- Bus signals: look up in signal groups
      else match busWireMap.find? (fun (wn, _, _) => wn == wireName) with
        | some (_, baseName, idx) => s!"        &{baseName}_[{idx}]"
        | none => s!"        &{wireName}_"
  )

  s!"// Auto-generated Lean gate-level simulation. DO NOT EDIT.\n" ++
  s!"// Generated from circuit: {c.name}\n" ++
  s!"#include \"lean_sim_{c.name}.h\"\n" ++
  s!"#include \"cpu_setup_{c.name}.h\"\n" ++
  "#include \"elf_loader.h\"\n" ++
  "#include <cstring>\n" ++
  "#include <cstdio>\n\n" ++

  "// ============================================================================\n" ++
  "// Bus helpers\n" ++
  "// ============================================================================\n\n" ++
  s!"uint32_t LeanSim::read_bus(bool** sigs, int bits) {lb}\n" ++
  "    uint32_t v = 0;\n" ++
  "    for (int i = 0; i < bits; i++)\n" ++
  "        v |= (*sigs[i] ? 1u : 0u) << i;\n" ++
  "    return v;\n" ++
  s!"{rb}\n\n" ++
  s!"void LeanSim::write_bus(bool** sigs, uint32_t val, int bits) {lb}\n" ++
  "    for (int i = 0; i < bits; i++)\n" ++
  "        *sigs[i] = (val >> i) & 1;\n" ++
  s!"{rb}\n\n" ++

  "// ============================================================================\n" ++
  "// Memory models\n" ++
  "// ============================================================================\n\n" ++

  (if !isCached then
    -- Non-cached: imem + dmem
    "static constexpr uint32_t TOHOST_ADDR = 0x" ++ natToHexDigits cfg.tohostAddr ++ ";\n" ++
    (match cfg.putcharAddr with
     | some addr => "static constexpr uint32_t PUTCHAR_ADDR = 0x" ++ natToHexDigits addr ++ ";\n"
     | none => "") ++
    "\n" ++
    s!"void LeanSim::imem_update() {lb}\n" ++
    "    uint32_t pc = read_bus(fetch_pc_sigs_, 32);\n" ++
    "    uint32_t widx = pc / 4;\n" ++
    "    uint32_t word = (widx < MEM_SIZE_WORDS) ? mem_[widx] : 0;\n" ++
    "    write_bus(imem_resp_data_sigs_, word, 32);\n" ++
    s!"{rb}\n\n" ++
    s!"void LeanSim::dmem_tick(bool req_valid, bool req_we,\n" ++
    s!"                          uint32_t addr, uint32_t data, uint32_t size) {lb}\n" ++
    "    dmem_req_ready_ = true;\n\n" ++
    "    if (dmem_pending_) " ++ lb ++ "\n" ++
    "        dmem_resp_valid_ = true;\n" ++
    "        write_bus(dmem_resp_data_sigs_, dmem_read_data_, 32);\n" ++
    "        dmem_pending_ = false;\n" ++
    "    " ++ rb ++ " else " ++ lb ++ "\n" ++
    "        dmem_resp_valid_ = false;\n" ++
    "        write_bus(dmem_resp_data_sigs_, dmem_read_data_, 32);\n" ++
    "    " ++ rb ++ "\n\n" ++
    "    if (req_valid) " ++ lb ++ "\n" ++
    "        if (req_we) " ++ lb ++ "\n" ++
    "            if (addr == TOHOST_ADDR) " ++ lb ++ "\n" ++
    "                test_done_ = true;\n" ++
    "                test_data_ = data;\n" ++
    (match cfg.putcharAddr with
     | some _ =>
       "            " ++ rb ++ " else if (addr == PUTCHAR_ADDR) " ++ lb ++ "\n" ++
       "                putchar(data & 0xFF);\n"
     | none => "") ++
    "            " ++ rb ++ " else " ++ lb ++ "\n" ++
    "                uint32_t widx = addr / 4;\n" ++
    "                if (widx < MEM_SIZE_WORDS) " ++ lb ++ "\n" ++
    "                    uint32_t cur = mem_[widx];\n" ++
    "                    uint32_t byte_off = addr & 3;\n" ++
    "                    if (size == 0) " ++ lb ++ " // SB\n" ++
    "                        uint32_t shift = byte_off * 8;\n" ++
    "                        cur = (cur & ~(0xFFu << shift)) | ((data & 0xFF) << shift);\n" ++
    "                    " ++ rb ++ " else if (size == 1) " ++ lb ++ " // SH\n" ++
    "                        uint32_t shift = (byte_off & 2) * 8;\n" ++
    "                        cur = (cur & ~(0xFFFFu << shift)) | ((data & 0xFFFF) << shift);\n" ++
    "                    " ++ rb ++ " else " ++ lb ++ " // SW\n" ++
    "                        cur = data;\n" ++
    "                    " ++ rb ++ "\n" ++
    "                    mem_[widx] = cur;\n" ++
    "                " ++ rb ++ "\n" ++
    "            " ++ rb ++ "\n" ++
    "        " ++ rb ++ " else " ++ lb ++ "\n" ++
    "            uint32_t ridx = addr / 4;\n" ++
    "            dmem_read_data_ = (ridx < MEM_SIZE_WORDS) ? mem_[ridx] : 0;\n" ++
    "            dmem_pending_ = true;\n" ++
    "        " ++ rb ++ "\n" ++
    "    " ++ rb ++ "\n" ++
    s!"{rb}\n\n" ++
    s!"void LeanSim::settle() {lb}\n" ++
    "    for (int i = 0; i < 3; i++) " ++ lb ++ "\n" ++
    "        imem_update();\n" ++
    "        cpu_eval_comb_all(ctx_);\n" ++
    "    " ++ rb ++ "\n" ++
    s!"{rb}\n\n"
   else
    -- Cached: cache-line memory
    "static constexpr uint32_t TOHOST_ADDR = 0x" ++ natToHexDigits cfg.tohostAddr ++ ";\n" ++
    (match cfg.putcharAddr with
     | some addr => "static constexpr uint32_t PUTCHAR_ADDR = 0x" ++ natToHexDigits addr ++ ";\n"
     | none => "") ++
    "\n" ++
    s!"void LeanSim::mem_tick(bool req_valid, bool req_we,\n" ++
    s!"                        uint32_t addr, uint32_t* data_line) {lb}\n" ++
    "    if (mem_pending_) " ++ lb ++ "\n" ++
    "        mem_resp_valid_ = true;\n" ++
    "        for (int w = 0; w < 8; w++)\n" ++
    "            write_bus(&mem_resp_data_sigs_[w * 32], mem_read_line_[w], 32);\n" ++
    "        mem_pending_ = false;\n" ++
    "    " ++ rb ++ " else " ++ lb ++ "\n" ++
    "        mem_resp_valid_ = false;\n" ++
    "    " ++ rb ++ "\n\n" ++
    "    if (req_valid) " ++ lb ++ "\n" ++
    "        if (req_we) " ++ lb ++ "\n" ++
    "            // Write 8-word cache line\n" ++
    "            uint32_t widx = addr / 4;\n" ++
    "            for (int w = 0; w < 8; w++) " ++ lb ++ "\n" ++
    "                if (widx + w < MEM_SIZE_WORDS)\n" ++
    "                    mem_[widx + w] = data_line[w];\n" ++
    "            " ++ rb ++ "\n" ++
    "        " ++ rb ++ " else " ++ lb ++ "\n" ++
    "            // Read 8-word cache line\n" ++
    "            uint32_t widx = addr / 4;\n" ++
    "            for (int w = 0; w < 8; w++)\n" ++
    "                mem_read_line_[w] = (widx + w < MEM_SIZE_WORDS) ? mem_[widx + w] : 0;\n" ++
    "            mem_pending_ = true;\n" ++
    "        " ++ rb ++ "\n" ++
    "    " ++ rb ++ "\n" ++
    s!"{rb}\n\n" ++
    s!"void LeanSim::settle() {lb}\n" ++
    "    for (int i = 0; i < 3; i++)\n" ++
    "        cpu_eval_comb_all(ctx_);\n" ++
    s!"{rb}\n\n") ++

  "// ============================================================================\n" ++
  "// Constructor\n" ++
  "// ============================================================================\n\n" ++
  s!"LeanSim::LeanSim(const std::string& elf_path) {lb}\n" ++
  "    // Initialize signal pointer arrays\n" ++
  (String.intercalate "\n" (
    groups.map fun sg =>
      s!"    for (int i = 0; i < {sg.width}; i++) {sg.name}_sigs_[i] = &{sg.name}_[i];")) ++ "\n" ++
  "\n" ++
  "    // Build the port pointer array matching the cpu_setup port order\n" ++
  s!"    bool* cpu_ports[] = {lb}\n" ++
  portPtrEntries ++ "\n" ++
  s!"    {rb};\n\n" ++
  s!"    ctx_ = cpu_create(\"lean_sim\", &reset_sig_, cpu_ports, {portList.length});\n\n" ++
  "    // Load ELF into memory\n" ++
  "    load_elf(elf_path.c_str(), [this](uint32_t addr, uint32_t data) " ++ lb ++ "\n" ++
  "        uint32_t widx = addr / 4;\n" ++
  "        if (widx < MEM_SIZE_WORDS) mem_[widx] = data;\n" ++
  "    " ++ rb ++ ");\n\n" ++
  "    // Reset phase\n" ++
  "    reset_sig_ = true;\n" ++
  (if !isCached then "    dmem_req_ready_ = true;\n" else "") ++
  "    for (int i = 0; i < 5; i++) " ++ lb ++ "\n" ++
  "        cpu_eval_seq_sample_all(ctx_);\n" ++
  "        cpu_eval_seq_all(ctx_);\n" ++
  "        settle();\n" ++
  "    " ++ rb ++ "\n" ++
  "    reset_sig_ = false;\n" ++
  "    settle();\n" ++
  s!"{rb}\n\n" ++

  s!"LeanSim::~LeanSim() {lb}\n" ++
  "    if (ctx_) cpu_delete(ctx_);\n" ++
  s!"{rb}\n\n" ++

  "// ============================================================================\n" ++
  "// Step: run cycles until next RVVI retirement\n" ++
  "// ============================================================================\n\n" ++
  s!"LeanSimStepResult LeanSim::step() {lb}\n" ++
  "    while (cycle_ < MAX_CYCLES) " ++ lb ++ "\n" ++
  (if !isCached then
    "        bool snap_req_valid = dmem_req_valid_;\n" ++
    "        bool snap_req_we = dmem_req_we_;\n" ++
    "        uint32_t snap_addr = read_bus(dmem_req_addr_sigs_, 32);\n" ++
    "        uint32_t snap_data = read_bus(dmem_req_data_sigs_, 32);\n" ++
    "        uint32_t snap_size = read_bus(dmem_req_size_sigs_, 2);\n"
   else
    "        bool snap_req_valid = mem_req_valid_;\n" ++
    "        bool snap_req_we = mem_req_we_;\n" ++
    "        uint32_t snap_addr = read_bus(mem_req_addr_sigs_, 32);\n" ++
    "        uint32_t snap_data_line[8];\n" ++
    "        for (int w = 0; w < 8; w++)\n" ++
    "            snap_data_line[w] = read_bus(&mem_req_data_sigs_[w * 32], 32);\n") ++
  "\n" ++
  "        cpu_eval_seq_sample_all(ctx_);\n" ++
  "        cpu_eval_seq_all(ctx_);\n\n" ++
  (if !isCached then
    "        dmem_tick(snap_req_valid, snap_req_we, snap_addr, snap_data, snap_size);\n"
   else
    "        mem_tick(snap_req_valid, snap_req_we, snap_addr, snap_data_line);\n") ++
  "        settle();\n" ++
  "        cycle_++;\n\n" ++
  (if isCached then
    "        // Check store snoop for tohost\n" ++
    "        if (store_snoop_valid_) " ++ lb ++ "\n" ++
    "            uint32_t snoop_addr = read_bus(store_snoop_addr_sigs_, 32);\n" ++
    "            uint32_t snoop_data = read_bus(store_snoop_data_sigs_, 32);\n" ++
    "            if (snoop_addr == TOHOST_ADDR) " ++ lb ++ "\n" ++
    "                test_done_ = true;\n" ++
    "                test_data_ = snoop_data;\n" ++
    "            " ++ rb ++ "\n" ++
    (match cfg.putcharAddr with
     | some _ =>
       "            if (snoop_addr == PUTCHAR_ADDR)\n" ++
       "                putchar(snoop_data & 0xFF);\n"
     | none => "") ++
    "        " ++ rb ++ "\n\n"
   else "") ++
  "        if (" ++ rvviValidName ++ "_) " ++ lb ++ "\n" ++
  "            LeanSimStepResult r = " ++ lb ++ rb ++ ";\n" ++
  s!"            r.pc       = read_bus({rvviPcBus}_sigs_, 32);\n" ++
  s!"            r.insn     = read_bus({rvviInsnBus}_sigs_, 32);\n" ++
  s!"            r.rd       = read_bus({rvviRdBus}_sigs_, 5);\n" ++
  s!"            r.rd_valid = {rvviRdValidName}_;\n" ++
  s!"            r.rd_data  = read_bus({rvviRdDataBus}_sigs_, 32);\n" ++
  (if groupExists rvviFrdBus then
     s!"            r.frd      = read_bus({rvviFrdBus}_sigs_, 5);\n" ++
     s!"            r.frd_valid = {if portExists "rvvi_frd_valid" then "rvvi_frd_valid_" else "rvvi_frd_validS0_" };\n" ++
     s!"            r.frd_data = read_bus({rvviFrdDataBus}_sigs_, 32);\n"
   else
     "            r.frd      = 0;\n" ++
     "            r.frd_valid = false;\n" ++
     "            r.frd_data = 0;\n") ++
  (if hasFFlags then
     "            r.fflags   = read_bus(fflags_acc_sigs_, 5);\n"
   else
     "            r.fflags   = 0;\n") ++
  "            r.done     = test_done_;\n" ++
  "            r.tohost   = test_data_;\n" ++
  "            return r;\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        if (test_done_) " ++ lb ++ "\n" ++
  "            LeanSimStepResult r = " ++ lb ++ rb ++ ";\n" ++
  "            r.done = true;\n" ++
  "            r.tohost = test_data_;\n" ++
  "            return r;\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ "\n\n" ++
  "    LeanSimStepResult r = " ++ lb ++ rb ++ ";\n" ++
  "    r.done = true;\n" ++
  "    r.tohost = 0;\n" ++
  "    return r;\n" ++
  s!"{rb}\n"

/--
  Standalone driver for the LeanSim gate-level C++ model.

  Same CLI as `toSimMainCpp` (`+elf`, `+timeout`, `+verbose`) and prints the
  same summary block (Cycle/Retired/IPC/tohost + TEST PASS/FAIL) so
  `run-suite.sh` parses its output unchanged and the benchmark ELFs can be run
  against the model as well as the RTL. Each `step()` retires at most one
  instruction; putchar is handled inside `LeanSim::step` already.
-/
def toLeanSimMainCpp (cfg : TestbenchConfig) : String :=
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let lb := "{"
  let rb := "}"

  "//==============================================================================\n" ++
  s!"// lean_sim_main_{tbName}.cpp - Auto-generated LeanSim standalone driver\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstring>\n\n" ++
  s!"#include \"lean_sim_{cfg.circuit.name}.h\"\n\n" ++
  "static const uint32_t DEFAULT_TIMEOUT = " ++ toString cfg.timeoutCycles ++ ";\n\n" ++
  "static const char* get_plusarg(int argc, char** argv, const char* name) " ++ lb ++ "\n" ++
  "    size_t len = strlen(name);\n" ++
  "    for (int i = 1; i < argc; i++)\n" ++
  "        if (strncmp(argv[i], name, len) == 0 && argv[i][len] == '=')\n" ++
  "            return argv[i] + len + 1;\n" ++
  "    return nullptr;\n" ++
  rb ++ "\n\n" ++
  "static bool has_plusarg(int argc, char** argv, const char* name) " ++ lb ++ "\n" ++
  "    for (int i = 1; i < argc; i++)\n" ++
  "        if (strcmp(argv[i], name) == 0) return true;\n" ++
  "    return false;\n" ++
  rb ++ "\n\n" ++

  s!"int main(int argc, char** argv) {lb}\n" ++
  "    const char* elf_path = get_plusarg(argc, argv, \"+elf\");\n" ++
  "    const char* timeout_str = get_plusarg(argc, argv, \"+timeout\");\n" ++
  "    bool verbose = has_plusarg(argc, argv, \"+verbose\");\n" ++
  "    uint32_t timeout = timeout_str ? atoi(timeout_str) : DEFAULT_TIMEOUT;\n\n" ++
  "    if (!elf_path) " ++ lb ++ "\n" ++
  "        fprintf(stderr, \"ERROR: No ELF file. Use +elf=path\\n\");\n" ++
  "        return 1;\n" ++
  "    " ++ rb ++ "\n\n" ++
  s!"    LeanSim sim(elf_path);\n\n" ++
  "    uint32_t retired = 0;\n" ++
  "    bool timed_out = false;\n" ++
  "    LeanSimStepResult r;\n\n" ++
  "    printf(\"Simulation started (timeout=%u cycles)\\n\", timeout);\n" ++
  "    printf(\"─────────────────────────────────────────────\\n\");\n\n" ++
  "    while (true) " ++ lb ++ "\n" ++
  "        r = sim.step();\n" ++
  "        if (r.done) break;\n" ++
  "        retired++;\n" ++
  "        if (sim.cycle() >= timeout) " ++ lb ++ " timed_out = true; break; " ++ rb ++ "\n" ++
  "        if (verbose)\n" ++
  "            printf(\"  RET[cy%u #%u] PC=0x%08x insn=0x%08x rd=x%u(%d) data=0x%016lx\\n\",\n" ++
  "                sim.cycle(), retired, r.pc, r.insn,\n" ++
  "                r.rd, (int)r.rd_valid, (unsigned long)r.rd_data);\n" ++
  "    " ++ rb ++ "\n\n" ++
  "    uint32_t cycle = sim.cycle();\n" ++
  "    bool passed = (r.tohost == 1);\n" ++
  "    printf(\"\\n══════ TEST %s ══════\\n\", passed ? \"PASS\" : \"FAIL\");\n" ++
  "    if (timed_out) printf(\"\\n══════ TIMEOUT ══════\\n\");\n" ++
  "    printf(\"  Cycle:     %u\\n\", cycle);\n" ++
  "    printf(\"  Retired:   %u\\n\", retired);\n" ++
  "    printf(\"  IPC:       %.3f\\n\", cycle > 0 ? (double)retired / cycle : 0.0);\n" ++
  "    printf(\"  tohost:    0x%08x\\n\", r.tohost);\n" ++
  "    printf(\"─────────────────────────────────────────────\\n\");\n" ++
  "    printf(\"Total cycles: %u\\n\", cycle);\n" ++
  "    printf(\"Total retired: %u\\n\", retired);\n" ++
  "    printf(\"IPC: %.3f\\n\", cycle > 0 ? (double)retired / cycle : 0.0);\n" ++
  "    return passed ? 0 : 1;\n" ++
  rb ++ "\n"

/-! ## Verilator cosim_main.cpp Generator -/

/-- Generate cosim_main.cpp for Verilator cosimulation, templated on testbench config. -/
def toCosimMainCpp (cfg : TestbenchConfig) : String :=
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let vType := s!"V{tbName}"
  let lb := "{"
  let rb := "}"

  "//==============================================================================\n" ++
  s!"// cosim_main_{tbName}.cpp - Auto-generated lock-step cosimulation driver\n" ++
  "// DO NOT EDIT - regenerate with: lake exe generate_all\n" ++
  "//==============================================================================\n\n" ++
  "#include <cstdio>\n" ++
  "#include <cstdlib>\n" ++
  "#include <cstring>\n" ++
  "#include <memory>\n" ++
  "#include <vector>\n" ++
  "#include <elf.h>\n\n" ++
  s!"#include \"{vType}.h\"\n" ++
  "#include \"verilated.h\"\n" ++
  "#include \"svdpi.h\"\n\n" ++
  "#include \"lib/spike_oracle.h\"\n" ++
  (if cfg.cacheLineMemPort.isNone then
    s!"#include \"lean_sim_{cfg.circuit.name}.h\"\n\n"
  else
    "\n") ++
  "extern \"C\" void dpi_mem_write(unsigned int word_addr, unsigned int data);\n" ++
  "extern \"C\" void dpi_set_tohost_addr(unsigned int addr);\n" ++
  (match cfg.putcharAddr with
   | some _ => "extern \"C\" void dpi_set_putchar_addr(unsigned int addr);\n"
   | none => "") ++
  "extern \"C\" unsigned int dpi_mem_read(unsigned int word_addr);\n" ++
  "extern \"C\" unsigned int dpi_mem_wr_count();\n" ++
  "extern \"C\" unsigned int dpi_mem_wr_idx();\n" ++
  "extern \"C\" unsigned int dpi_mem_wr_words();\n" ++
  "static FILE* g_cosim_uart_tx_file = nullptr;\n" ++
  "extern \"C\" void dpi_uart_tx_byte(char data) " ++ lb ++ "\n" ++
  "    if (g_cosim_uart_tx_file) " ++ lb ++ "\n" ++
  "        fputc(data, g_cosim_uart_tx_file);\n" ++
  "        fflush(g_cosim_uart_tx_file);\n" ++
  "    " ++ rb ++ "\n" ++
  rb ++ "\n\n" ++
  "static const uint32_t DEFAULT_TIMEOUT = " ++ toString cfg.timeoutCycles ++ ";\n\n" ++
  "// Words in the harness memory; the full-memory diff walks this range.\n" ++
  "static const uint32_t MEM_SIZE_WORDS = " ++ toString cfg.memSizeWords ++ ";\n" ++
  "// A store still draining in one model shows a transient difference that\n" ++
  "// disappears when it lands.  Report only a divergence that outlives this.\n" ++
  "static const unsigned int MEM_PERSIST_CYCLES = 64;\n" ++
  "static const unsigned int MEM_NO_PENDING = 0xFFFFFFFFu;\n\n" ++

  "static const char* get_plusarg(int argc, char** argv, const char* name) " ++ lb ++ "\n" ++
  "    size_t len = strlen(name);\n" ++
  "    for (int i = 1; i < argc; i++)\n" ++
  "        if (strncmp(argv[i], name, len) == 0 && argv[i][len] == '=')\n" ++
  "            return argv[i] + len + 1;\n" ++
  "    return nullptr;\n" ++
  rb ++ "\n\n" ++

  "static int64_t elf_lookup_symbol(const char* path, const char* sym_name) " ++ lb ++ "\n" ++
  "    FILE* f = fopen(path, \"rb\");\n" ++
  "    if (!f) return -1;\n" ++
  "    unsigned char ident[EI_NIDENT];\n" ++
  "    if (fread(ident, 1, EI_NIDENT, f) != EI_NIDENT) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "    fseek(f, 0, SEEK_SET);\n" ++
  "    if (ident[EI_CLASS] == ELFCLASS64) " ++ lb ++ "\n" ++
  "        Elf64_Ehdr ehdr;\n" ++
  "        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "        for (int i = 0; i < ehdr.e_shnum; i++) " ++ lb ++ "\n" ++
  "            Elf64_Shdr shdr;\n" ++
  "            fseek(f, ehdr.e_shoff + i * ehdr.e_shentsize, SEEK_SET);\n" ++
  "            if (fread(&shdr, sizeof(shdr), 1, f) != 1) continue;\n" ++
  "            if (shdr.sh_type != SHT_SYMTAB) continue;\n" ++
  "            Elf64_Shdr strhdr;\n" ++
  "            fseek(f, ehdr.e_shoff + shdr.sh_link * ehdr.e_shentsize, SEEK_SET);\n" ++
  "            if (fread(&strhdr, sizeof(strhdr), 1, f) != 1) continue;\n" ++
  "            auto* strtab = new char[strhdr.sh_size];\n" ++
  "            fseek(f, strhdr.sh_offset, SEEK_SET);\n" ++
  "            if (fread(strtab, 1, strhdr.sh_size, f) != strhdr.sh_size) " ++ lb ++ " delete[] strtab; continue; " ++ rb ++ "\n" ++
  "            int nsyms = shdr.sh_size / shdr.sh_entsize;\n" ++
  "            for (int j = 0; j < nsyms; j++) " ++ lb ++ "\n" ++
  "                Elf64_Sym sym;\n" ++
  "                fseek(f, shdr.sh_offset + j * shdr.sh_entsize, SEEK_SET);\n" ++
  "                if (fread(&sym, sizeof(sym), 1, f) != 1) continue;\n" ++
  "                if (sym.st_name < strhdr.sh_size && strcmp(strtab + sym.st_name, sym_name) == 0) " ++ lb ++ "\n" ++
  "                    delete[] strtab; fclose(f); return (int64_t)sym.st_value;\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n" ++
  "            delete[] strtab;\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ " else " ++ lb ++ "\n" ++
  "        Elf32_Ehdr ehdr;\n" ++
  "        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "        for (int i = 0; i < ehdr.e_shnum; i++) " ++ lb ++ "\n" ++
  "            Elf32_Shdr shdr;\n" ++
  "            fseek(f, ehdr.e_shoff + i * ehdr.e_shentsize, SEEK_SET);\n" ++
  "            if (fread(&shdr, sizeof(shdr), 1, f) != 1) continue;\n" ++
  "            if (shdr.sh_type != SHT_SYMTAB) continue;\n" ++
  "            Elf32_Shdr strhdr;\n" ++
  "            fseek(f, ehdr.e_shoff + shdr.sh_link * ehdr.e_shentsize, SEEK_SET);\n" ++
  "            if (fread(&strhdr, sizeof(strhdr), 1, f) != 1) continue;\n" ++
  "            auto* strtab = new char[strhdr.sh_size];\n" ++
  "            fseek(f, strhdr.sh_offset, SEEK_SET);\n" ++
  "            if (fread(strtab, 1, strhdr.sh_size, f) != strhdr.sh_size) " ++ lb ++ " delete[] strtab; continue; " ++ rb ++ "\n" ++
  "            int nsyms = shdr.sh_size / shdr.sh_entsize;\n" ++
  "            for (int j = 0; j < nsyms; j++) " ++ lb ++ "\n" ++
  "                Elf32_Sym sym;\n" ++
  "                fseek(f, shdr.sh_offset + j * shdr.sh_entsize, SEEK_SET);\n" ++
  "                if (fread(&sym, sizeof(sym), 1, f) != 1) continue;\n" ++
  "                if (sym.st_name < strhdr.sh_size && strcmp(strtab + sym.st_name, sym_name) == 0) " ++ lb ++ "\n" ++
  "                    delete[] strtab; fclose(f); return (int64_t)sym.st_value;\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n" ++
  "            delete[] strtab;\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ "\n" ++
  "    fclose(f);\n" ++
  "    return -1;\n" ++
  rb ++ "\n\n" ++

  "static int load_elf(const char* path) " ++ lb ++ "\n" ++
  "    FILE* f = fopen(path, \"rb\");\n" ++
  "    if (!f) " ++ lb ++ " fprintf(stderr, \"ERROR: Cannot open ELF: %s\\n\", path); return -1; " ++ rb ++ "\n" ++
  "    unsigned char ident[EI_NIDENT];\n" ++
  "    if (fread(ident, 1, EI_NIDENT, f) != EI_NIDENT) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "    if (memcmp(ident, ELFMAG, SELFMAG) != 0) " ++ lb ++ "\n" ++
  "        fprintf(stderr, \"ERROR: Not an ELF file\\n\"); fclose(f); return -1;\n" ++
  "    " ++ rb ++ "\n" ++
  "    fseek(f, 0, SEEK_SET);\n" ++
  "    uint32_t total = 0;\n" ++
  "    if (ident[EI_CLASS] == ELFCLASS64) " ++ lb ++ "\n" ++
  "        Elf64_Ehdr ehdr;\n" ++
  "        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "        for (int i = 0; i < ehdr.e_phnum; i++) " ++ lb ++ "\n" ++
  "            Elf64_Phdr phdr;\n" ++
  "            fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);\n" ++
  "            if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;\n" ++
  "            if (phdr.p_type != PT_LOAD || phdr.p_memsz == 0) continue;\n" ++
  "            for (uint64_t off = 0; off < phdr.p_memsz; off += 4)\n" ++
  "                dpi_mem_write((phdr.p_paddr + off) / 4, 0);\n" ++
  "            if (phdr.p_filesz > 0) " ++ lb ++ "\n" ++
  "                fseek(f, phdr.p_offset, SEEK_SET);\n" ++
  "                uint64_t words = (phdr.p_filesz + 3) / 4;\n" ++
  "                for (uint64_t w = 0; w < words; w++) " ++ lb ++ "\n" ++
  "                    uint32_t word = 0;\n" ++
  "                    uint64_t rem = phdr.p_filesz - w * 4;\n" ++
  "                    (void)fread(&word, 1, rem < 4 ? rem : 4, f);\n" ++
  "                    dpi_mem_write((phdr.p_paddr / 4) + w, word);\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n" ++
  "            total += phdr.p_memsz;\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ " else " ++ lb ++ "\n" ++
  "        Elf32_Ehdr ehdr;\n" ++
  "        if (fread(&ehdr, sizeof(ehdr), 1, f) != 1) " ++ lb ++ " fclose(f); return -1; " ++ rb ++ "\n" ++
  "        for (int i = 0; i < ehdr.e_phnum; i++) " ++ lb ++ "\n" ++
  "            Elf32_Phdr phdr;\n" ++
  "            fseek(f, ehdr.e_phoff + i * ehdr.e_phentsize, SEEK_SET);\n" ++
  "            if (fread(&phdr, sizeof(phdr), 1, f) != 1) continue;\n" ++
  "            if (phdr.p_type != PT_LOAD || phdr.p_memsz == 0) continue;\n" ++
  "            for (uint32_t off = 0; off < phdr.p_memsz; off += 4)\n" ++
  "                dpi_mem_write((phdr.p_paddr + off) / 4, 0);\n" ++
  "            if (phdr.p_filesz > 0) " ++ lb ++ "\n" ++
  "                fseek(f, phdr.p_offset, SEEK_SET);\n" ++
  "                uint32_t words = (phdr.p_filesz + 3) / 4;\n" ++
  "                for (uint32_t w = 0; w < words; w++) " ++ lb ++ "\n" ++
  "                    uint32_t word = 0;\n" ++
  "                    uint32_t rem = phdr.p_filesz - w * 4;\n" ++
  "                    (void)fread(&word, 1, rem < 4 ? rem : 4, f);\n" ++
  "                    dpi_mem_write((phdr.p_paddr / 4) + w, word);\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n" ++
  "            total += phdr.p_memsz;\n" ++
  "        " ++ rb ++ "\n" ++
  "    " ++ rb ++ "\n" ++
  "    fclose(f);\n" ++
  "    return 0;\n" ++
  rb ++ "\n\n" ++

  "static bool is_clint_load(uint32_t insn, uint64_t rs1_value) " ++ lb ++ "\n" ++
  "    if ((insn & 0x7f) != 0x03) return false; // not a load\n" ++
  "    int32_t imm = (int32_t)insn >> 20;\n" ++
  "    uint64_t addr = rs1_value + (int64_t)imm;\n" ++
  "    return addr >= 0x02000000 && addr < 0x02010000;\n" ++
  rb ++ "\n\n" ++

  "// A write to fflags/frm/fcsr changes the architectural flag value during the\n" ++
  "// instruction itself, and the RTL reports the registered value at the retire\n" ++
  "// cycle, so the write itself always diverges.  Excluding it is safe: the\n" ++
  "// next FP instruction observes the written value and its flags are compared.\n" ++
  "static bool is_fcsr_write(uint32_t insn) " ++ lb ++ "\n" ++
  "    if ((insn & 0x7f) != 0x73) return false;\n" ++
  "    if (((insn >> 12) & 0x7) == 0) return false;\n" ++
  "    uint32_t csr_addr = (insn >> 20) & 0xfff;\n" ++
  "    return csr_addr == 0x001 || csr_addr == 0x002 || csr_addr == 0x003;\n" ++
  rb ++ "\n\n" ++

  "static bool is_unsyncable_csr_read(uint32_t insn) " ++ lb ++ "\n" ++
  "    uint32_t opcode = insn & 0x7f;\n" ++
  "    if (opcode != 0x73) return false;\n" ++
  "    uint32_t funct3 = (insn >> 12) & 0x7;\n" ++
  "    if (funct3 == 0) return false;\n" ++
  "    uint32_t csr_addr = (insn >> 20) & 0xfff;\n" ++
  "    // Performance counters (cycle/instret differ due to OoO timing)\n" ++
  "    if (csr_addr == 0xB00 || csr_addr == 0xB02 || csr_addr == 0xB80 || csr_addr == 0xB82 ||\n" ++
  "        csr_addr == 0xC00 || csr_addr == 0xC02 || csr_addr == 0xC80 || csr_addr == 0xC82)\n" ++
  "        return true;\n" ++
  "    // Trap-related and status CSRs (mstatus, mie, mtvec, mscratch, mepc, mcause, mtval, mip)\n" ++
  "    if (csr_addr == 0x300 || csr_addr == 0x304 || csr_addr == 0x305 || csr_addr == 0x340 ||\n" ++
  "        csr_addr == 0x341 || csr_addr == 0x342 || csr_addr == 0x343 || csr_addr == 0x344)\n" ++
  "        return true;\n" ++
  "    return false;\n" ++
  rb ++ "\n\n" ++

  "static uint32_t find_tohost_addr(const char* path) " ++ lb ++ "\n" ++
  "    int64_t addr = elf_lookup_symbol(path, \"tohost\");\n" ++
  "    return (addr >= 0) ? (uint32_t)addr : 0x1000;\n" ++
  rb ++ "\n\n" ++

  "struct RVVIState " ++ lb ++ "\n" ++
  "    bool valid, trap, rd_valid, frd_valid, is_fp;\n" ++
  "    uint64_t pc;\n" ++
  "    uint32_t insn, rd;\n" ++
  "    uint64_t rd_data;\n" ++
  "    uint32_t frd;\n" ++
  "    uint64_t frd_data;\n" ++
  "    uint32_t fflags;\n" ++
  rb ++ ";\n\n" ++

  s!"static void read_rvvi_dual(const {vType}* dut, RVVIState out[2]) {lb}\n" ++
  "    out[0] = " ++ lb ++ rb ++ ";\n" ++
  "    out[0].valid     = dut->o_rvvi_valid_0;\n" ++
  "    out[0].trap      = dut->o_rvvi_trap_0;\n" ++
  "    out[0].pc        = dut->o_rvvi_pc_rdata_0;\n" ++
  "    out[0].insn      = dut->o_rvvi_insn_0;\n" ++
  "    out[0].rd        = dut->o_rvvi_rd_0;\n" ++
  "    out[0].rd_valid  = dut->o_rvvi_rd_valid_0;\n" ++
  "    out[0].rd_data   = dut->o_rvvi_rd_data_0;\n" ++
  "    out[0].is_fp     = dut->o_rvvi_is_fp_0;\n" ++
  "    out[0].frd       = dut->o_rvvi_rd_0;\n" ++
  "    out[0].frd_valid = dut->o_rvvi_is_fp_0;\n" ++
  "    out[0].frd_data  = dut->o_rvvi_fp_rd_data;\n" ++
  "    out[1] = " ++ lb ++ rb ++ ";\n" ++
  "    out[1].valid     = dut->o_rvvi_valid_1;\n" ++
  "    out[1].trap      = dut->o_rvvi_trap_1;\n" ++
  "    out[1].pc        = dut->o_rvvi_pc_rdata_1;\n" ++
  "    out[1].insn      = dut->o_rvvi_insn_1;\n" ++
  "    out[1].rd        = dut->o_rvvi_rd_1;\n" ++
  "    out[1].rd_valid  = dut->o_rvvi_rd_valid_1;\n" ++
  "    out[1].rd_data   = dut->o_rvvi_rd_data_1;\n" ++
  "    out[1].is_fp     = dut->o_rvvi_is_fp_1;\n" ++
  "    out[1].frd       = dut->o_rvvi_rd_1;\n" ++
  "    out[1].frd_valid = dut->o_rvvi_is_fp_1;\n" ++
  "    out[1].frd_data  = dut->o_rvvi_fp_rd_data_slot1;\n" ++
  rb ++ "\n\n" ++

  s!"int main(int argc, char** argv) {lb}\n" ++
  "    Verilated::commandArgs(argc, argv);\n" ++
  "    const char* elf_path = get_plusarg(argc, argv, \"+elf\");\n" ++
  "    if (!elf_path) " ++ lb ++ "\n" ++
  "        fprintf(stderr, \"Usage: %s +elf=<path.elf> [+timeout=N]\\n\", argv[0]);\n" ++
  "        return 1;\n" ++
  "    " ++ rb ++ "\n" ++
  "    uint32_t timeout = DEFAULT_TIMEOUT;\n" ++
  "    const char* to = get_plusarg(argc, argv, \"+timeout\");\n" ++
  "    if (to) timeout = (uint32_t)atol(to);\n" ++
  "    const char* uart_log_path = get_plusarg(argc, argv, \"+uart_tx_log\");\n" ++
  "    if (uart_log_path) g_cosim_uart_tx_file = fopen(uart_log_path, \"wb\");\n\n" ++
  "    bool dump_spike = get_plusarg(argc, argv, \"+dump_spike\") != nullptr;\n" ++
  "    bool mem_diff_dump = get_plusarg(argc, argv, \"+mem_diff\") != nullptr;\n" ++
  "    bool sb_trace = get_plusarg(argc, argv, \"+sbtrace\") != nullptr;\n" ++
  "    bool csr_trace = get_plusarg(argc, argv, \"+csrtrace\") != nullptr;\n" ++
  "    bool atm_trace = get_plusarg(argc, argv, \"+atmtrace\") != nullptr;\n" ++
  "    // +ren_lo=N +ren_hi=M: per-cycle tag trace (alloc, CDB, free, mem RS src2).\n" ++
  "    const char* ren_lo_arg = get_plusarg(argc, argv, \"+ren_lo\");\n" ++
  "    const char* ren_hi_arg = get_plusarg(argc, argv, \"+ren_hi\");\n" ++
  "    unsigned long ren_lo = ren_lo_arg ? strtoul(ren_lo_arg, nullptr, 0) : 1;\n" ++
  "    unsigned long ren_hi = ren_hi_arg ? strtoul(ren_hi_arg, nullptr, 0) : 0;\n" ++
  "    // +mem_watch=0xADDR: compare one word every cycle and report each cycle\n" ++
  "    // where it starts to differ, with the instruction retiring then.  That\n" ++
  "    // names the store that should have written it.\n" ++
  "    uint64_t watch_addr = 0;\n" ++
  "    bool watch_en = false;\n" ++
  "    const char* watch_arg = get_plusarg(argc, argv, \"+mem_watch\");\n" ++
  "    if (watch_arg) " ++ lb ++ " watch_addr = strtoull(watch_arg, nullptr, 0); watch_en = true; " ++ rb ++ "\n" ++
  s!"    auto dut = std::make_unique<{vType}>();\n" ++
  "    dut->eval();\n" ++
  s!"    svSetScope(svGetScopeFromName(\"TOP.{tbName}\"));\n" ++
  "    if (load_elf(elf_path) != 0) return 1;\n" ++
  "    // The RTL's architectural memory: every store write it accepts at its\n" ++
  "    // memory port, in issue order.  A cache sits between the core and the\n" ++
  "    // harness array, so that array holds only what the cache evicted, and a\n" ++
  "    // comparison against it is blind to every store the cache absorbed.\n" ++
  "    static unsigned char rtl_shadow[1u << 20];\n" ++
  "    int load_bad = 0;\n" ++
  "    struct WRec { unsigned cy, addr; unsigned long long data; unsigned sz; };\n" ++
  "    static WRec wr_ring[64]; static unsigned wr_n = 0;\n" ++
  "    for (unsigned si = 0; si < MEM_SIZE_WORDS; si++) " ++ lb ++ "\n" ++
  "        unsigned sv0 = dpi_mem_read(si);\n" ++
  "        for (int sb = 0; sb < 4; sb++)\n" ++
  "            rtl_shadow[si*4 + sb] = (unsigned char)((sv0 >> (8*sb)) & 0xff);\n" ++
  "    " ++ rb ++ "\n\n" ++
  "    printf(\"Harness built %s %s\\n\", __DATE__, __TIME__);\n\n" ++
  s!"    auto spike = std::make_unique<SpikeOracle>(elf_path, \"{cfg.spikeIsa}\");\n" ++
  (if cfg.cacheLineMemPort.isNone then
    "    auto lean_sim = std::make_unique<LeanSim>(elf_path);\n\n"
  else "\n") ++
  "    dut->clk = 0; dut->rst_n = 0;\n" ++
  "    for (int i = 0; i < 10; i++) " ++ lb ++ " dut->clk = !dut->clk; dut->eval(); " ++ rb ++ "\n" ++
  "    dut->rst_n = 1;\n\n" ++
  "    uint32_t tohost_addr = find_tohost_addr(elf_path);\n" ++
  "    dpi_set_tohost_addr(tohost_addr);\n\n" ++
  (match cfg.putcharAddr with
   | some _ =>
     "    int64_t putchar_sym = elf_lookup_symbol(elf_path, \"putchar_addr\");\n" ++
     "    if (putchar_sym >= 0) dpi_set_putchar_addr((uint32_t)putchar_sym);\n\n"
   | none => "") ++
  "    uint64_t cycle = 0, retired = 0, mismatches = 0, fflag_mismatches = 0;\n" ++
  "    enum { WB_RING = 32 };\n" ++
  "    struct WbRec { unsigned cy; unsigned lane; unsigned tag; unsigned long long data; };\n" ++
  "    WbRec wb_ring[WB_RING]; unsigned wb_n = 0;\n" ++
  "    struct ReqRec { unsigned cy; unsigned aw; unsigned we; unsigned v; unsigned addr; };\n" ++
  "    ReqRec req_ring[WB_RING]; unsigned req_n = 0;\n" ++

  "    uint64_t mem_mismatches = 0;\n" ++
  "    // Instructions Spike executed to resynchronise that the RTL did not.
" ++
  "    // While that count moves the two memories are not comparable.
" ++
  "    unsigned long resync_steps = 0;\n" ++
  "    int resync_reports = 0;\n" ++
  "    int fp_mismatch_prints = 0;\n" ++
  "    unsigned int last_wr_count = 0;\n" ++
  "    unsigned int pending_addr = MEM_NO_PENDING, pending_age = 0;\n" ++
  "    int watch_reports = 0;\n" ++
  "    uint32_t watch_rtl_prev = 0, watch_spike_prev = 0;\n" ++
  "    uint64_t last_pc = 0;\n" ++
  "    uint32_t last_insn = 0;\n" ++
  "    int sync_grace = 0;\n" ++
  "    int sb_trace_lines = 0;\n" ++
  "    int csr_trace_lines = 0;\n" ++
  "    int atm_trace_lines = 0;\n" ++
  "    bool done = false;\n\n" ++
  "    while (!done && cycle < timeout) " ++ lb ++ "\n" ++
  "        dut->clk = 1; dut->eval();\n" ++
  "        RVVIState rvvi[2];\n" ++
  "        read_rvvi_dual(dut.get(), rvvi);\n\n" ++
  "        // Store-buffer event trace (+sbtrace): every cycle the buffer\n" ++
  "        // enqueues, commits or dequeues, print the buffer's accounting so a\n" ++
  "        // leak (an entry that never earns its commit) is visible.\n" ++
  "        if (sb_trace && sb_trace_lines < 600) " ++ lb ++ "\n" ++
  "            unsigned long long s = dut->o_dbg_sb, a = dut->o_dbg_amo;\n" ++
  "            unsigned enq = (s >> 14) & 1, deq = (s >> 15) & 1, ceg = (s >> 16) & 1;\n" ++
  "            unsigned cs0 = (s >> 12) & 1, cs1 = (s >> 13) & 1, flp = (s >> 19) & 1;\n" ++
  "            if (enq | deq | ceg | cs0 | cs1 | flp) " ++ lb ++ "\n" ++
  "                printf(\"SBT cy=%lu enq=%u ceg=%u deq=%u cs0=%u cs1=%u ctv=%u deqv=%u flp=%u\"\n" ++
  "                       \" v=%02llx c=%02llx head=%llu tail=%llu cptr=%llu cnt=%llu pnd=%llu csp=%llu idx=%llu alloc=%llu\"\n" ++
  "                       \" rI0=%llu rI1=%llu rS0=%llu rS1=%llu ret0=%u ret1=%u\"\n" ++
  "                       \" amo=%u sc=%u ld=%u rsq=%u sbq=%u mde=%u dok=%u busy=%u aw=%u empt=%u\\n\",\n" ++
  "                    cycle, enq, ceg, deq, cs0, cs1, (s >> 17) & 1, (s >> 18) & 1, flp,\n" ++
  "                    s & 0xff, (s >> 8) & 0xff, (s >> 35) & 7, (s >> 38) & 7, (s >> 41) & 7,\n" ++
  "                    (s >> 31) & 0xf, (s >> 28) & 7, (s >> 25) & 7, (s >> 22) & 7, (s >> 44) & 7,\n" ++
  "                    (s >> 4) & 0xf, s & 0xf, (s >> 9) & 1, (s >> 8) & 1, (s >> 10) & 1, (s >> 11) & 1,\n" ++
  "                    (a >> 24) & 1, (a >> 29) & 1, (a >> 28) & 1, (a >> 26) & 1, (a >> 20) & 1,\n" ++
  "                    (a >> 14) & 1, (a >> 22) & 1, (a >> 23) & 1, (a >> 21) & 1);\n" ++
  "                sb_trace_lines++;\n" ++
  "            " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        // CSR capture trace (+csrtrace): every cycle the serialize FSM takes\n" ++
  "        // a CSR instruction, print the latches it took.  A latch taken one\n" ++
  "        // cycle late names a younger instruction's fields.\n" ++
  "        if (csr_trace && csr_trace_lines < 400) " ++ lb ++ "\n" ++
  "            unsigned long long c = dut->o_dbg_csr;\n" ++
  "            unsigned fi_start = (c >> 39) & 1, sel = (c >> 38) & 1, det = (c >> 37) & 1;\n" ++
  "            unsigned slot = (c >> 36) & 1;\n" ++
  "            if (fi_start | det) " ++ lb ++ "\n" ++
  "                printf(\"CSR cy=%lu fi_start=%u det=%u sel=%u slot=%u addr=0x%03llx ph=%llu rd=%llu flag=%u ren=%u dc=%u drain=%u useq=%u data=0x%08llx\\n\",\n" ++
  "                    cycle, fi_start, det, sel, slot, (c >> 52) & 0xfff, (c >> 46) & 0x3f, (c >> 41) & 0x1f,\n" ++
  "                    (c >> 40) & 1, (c >> 35) & 1, (c >> 34) & 1, (c >> 33) & 1, (c >> 32) & 1, c & 0xffffffff);\n" ++
  "                csr_trace_lines++;\n" ++
  "            " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        // Tag trace (+ren_lo/+ren_hi): allocations, CDB broadcasts, frees and\n" ++
  "        // memory RS src2 capture.  Two live values on one physical tag show\n" ++
  "        // up as a tag freed or allocated while still mapped.\n" ++
  "        if (cycle >= ren_lo && cycle <= ren_hi) " ++ lb ++ "\n" ++
  "            unsigned long long r = dut->o_dbg_ren, r2 = dut->o_dbg_ren2, cd = dut->o_dbg_cdbd;\n" ++
  "            unsigned dbv = (r >> 12) & 3;\n" ++
  "            printf(\"REN cy=%lu\", cycle);\n" ++
  "            for (int s = 0; s < 2; s++) " ++ lb ++ "\n" ++
  "                if (!((dbv >> s) & 1)) continue;\n" ++
  "                printf(\" alloc%d[rd=x%llu p%llu hasrd=%llu force=%llu]\", s,\n" ++
  "                    (r2 >> (10 + 5 * s)) & 0x1f, (r >> (14 + 6 * s)) & 0x3f,\n" ++
  "                    (r >> (10 + s)) & 1, (r >> (8 + s)) & 1);\n" ++
  "            " ++ rb ++ "\n" ++
  "            for (int s = 0; s < 2; s++) " ++ lb ++ "\n" ++
  "                if (!((r >> (62 + s)) & 1)) continue;\n" ++
  "                printf(\" cdb%d[p%llu=0x%llx]\", s, (r >> (50 + 6 * s)) & 0x3f,\n" ++
  "                    (cd >> (32 * s)) & 0xffffffffull);\n" ++
  "            " ++ rb ++ "\n" ++
  "            for (int s = 0; s < 2; s++) " ++ lb ++ "\n" ++
  "                if (!((r >> (48 + s)) & 1)) continue;\n" ++
  "                printf(\" commit%d[free=%llu p%llu]\", s, (r >> (46 + s)) & 1,\n" ++
  "                    (r >> (34 + 6 * s)) & 0x3f);\n" ++
  "            " ++ rb ++ "\n" ++
  "            if ((r2 >> 56) & 1) printf(\" FI_START\");\n" ++
  "            if ((r2 >> 55) & 1) printf(\" FB_START\");\n" ++
  "            if ((r2 >> 54) & 1) printf(\" CSR_REN\");\n" ++
  "            if ((r2 >> 40) & 3)\n" ++
  "                printf(\" inject[%s cap_ph=p%llu cap_oph=p%llu]\", ((r2 >> 41) & 1) ? \"csr\" : \"fb\",\n" ++
  "                    (r2 >> 48) & 0x3f, (r2 >> 42) & 0x3f);\n" ++
  "            if ((r2 >> 39) & 1)\n" ++
  "                printf(\" cmt0mux[crat=%llu x%llu->p%llu free=%llu p%llu]\", (r2 >> 37) & 1,\n" ++
  "                    (r2 >> 20) & 0x1f, (r2 >> 25) & 0x3f, (r2 >> 38) & 1, (r2 >> 31) & 0x3f);\n" ++
  "            if ((r >> 33) & 1)\n" ++
  "                printf(\" memiss[s2=p%llu rdy=%llu]\", (r >> 26) & 0x3f, (r >> 32) & 1);\n" ++
  "            printf(\"\\n\");\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        // Atomic trace (+atmtrace): the address the RMW read from, the data\n" ++
  "        // the response carried, and the address it writes back to.  An\n" ++
  "        // atomic whose read address differs from its write address reports\n" ++
  "        // the wrong old value.\n" ++
  "        if (atm_trace && atm_trace_lines < 400) " ++ lb ++ "\n" ++
  "            unsigned long long t = dut->o_dbg_atm, f = dut->o_dbg_atmf;\n" ++
  "            unsigned long long g = dut->o_dbg_atmf2;\n" ++
  "            unsigned amo_resp = (g >> 3) & 1, aw_set = (g >> 6) & 1, lr_resp = (g >> 17) & 1;\n" ++
  "            unsigned rv = (g >> 0) & 1, lpend = (g >> 1) & 1, dreq = (g >> 7) & 1;\n" ++
  "            unsigned fl = (g >> 21) & 1, clr = (g >> 20) & 1;\n" ++
  "            if (amo_resp | aw_set | lr_resp | rv | dreq | clr) " ++ lb ++ "\n" ++
  "                printf(\"ATM cy=%lu amo_resp=%u aw_set=%u clr=%u lr_resp=%u mem_addr_r=0x%08llx aw_addr=0x%08llx req_addr=0x%08llx resp_data=0x%08llx busy=%u awp=%u rv=%u we=%u rl=%u lpend=%u lnf=%u isld=%u mvr=%u deqv=%u empt=%u dok=%u fl=%u\\n\",\n" ++
  "                    cycle, amo_resp, aw_set, clr, lr_resp, t & 0xffffffff, (t >> 32) & 0xffffffff,\n" ++
  "                    f & 0xffffffff, (f >> 32) & 0xffffffff,\n" ++
  "                    (g >> 2) & 1, (g >> 5) & 1, rv, (g >> 8) & 1, (g >> 4) & 1, lpend,\n" ++
  "                    (g >> 9) & 1, (g >> 10) & 1, (g >> 11) & 1,\n" ++
  "                    (g >> 12) & 1, (g >> 13) & 1, (g >> 14) & 1, fl);\n" ++
  "                atm_trace_lines++;\n" ++
  "            " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        for (int slot = 0; slot < 2; slot++) " ++ lb ++ "\n" ++
  "            if (!rvvi[slot].valid) continue;\n\n" ++  "            // Pre-step sync: handle WFI gaps and async interrupt timing differences.\n" ++
  "            bool sync_forced = (sync_grace > 0);\n" ++
  "            if (sync_grace > 0) sync_grace--;\n" ++
  "            if (spike->get_pc() != rvvi[slot].pc) " ++ lb ++ "\n" ++
  "                if (resync_reports < 16) " ++ lb ++ "\n" ++
  "                    fprintf(stderr, \"RESYNC ret#%lu cy%lu slot%d RTL_pc=0x%lx Spike_pc=0x%lx insn=0x%08x\\n\",\n" ++
  "                        retired, cycle, slot, (unsigned long)rvvi[slot].pc,\n" ++
  "                        (unsigned long)spike->get_pc(), rvvi[slot].insn);\n" ++
  "                    resync_reports++;\n" ++
  "                " ++ rb ++ "\n" ++
  "                auto saved = spike->save_state();\n" ++
  "                int catchup = 0;\n" ++
  "                while (spike->get_pc() != rvvi[slot].pc && catchup < 32) " ++ lb ++ "\n" ++
  "                    uint64_t before = spike->get_pc();\n" ++
  "                    spike->step(); catchup++; resync_steps++;\n" ++
  "                    if (spike->get_pc() == before) spike->unhalt();\n" ++
  "                " ++ rb ++ "\n" ++
  "                if (spike->get_pc() != rvvi[slot].pc) " ++ lb ++ "\n" ++
  "                    // Catchup failed: try forcing interrupt\n" ++
  "                    spike->restore_state(saved);\n" ++
  "                    spike->set_mip_mtip(true);\n" ++
  "                    for (int t = 0; t < 32 && spike->get_pc() != rvvi[slot].pc; t++) " ++ lb ++ "\n" ++
  "                        uint64_t before = spike->get_pc();\n" ++
  "                        spike->step();\n" ++
  "                        if (spike->get_pc() == before) spike->unhalt();\n" ++
  "                    " ++ rb ++ "\n" ++
  "                    spike->set_mip_mtip(false);\n" ++
  "                " ++ rb ++ "\n" ++
  "                if (spike->get_pc() != rvvi[slot].pc) " ++ lb ++ "\n" ++
  "                    // All sync attempts failed: force PC to maintain lockstep\n" ++
  "                    spike->set_pc(rvvi[slot].pc);\n" ++
  "                    spike->set_mip_mtip(false);\n" ++
  "                " ++ rb ++ "\n" ++
  "                // Any resync means register state may differ — suppress comparison\n" ++
  "                sync_forced = true;\n" ++
  "                sync_grace = 64;\n" ++
  "            " ++ rb ++ "\n\n" ++
  "            SpikeStepResult spike_r = spike->step();\n" ++
  "            int skip = 0;\n" ++
  "            while (spike_r.pc != rvvi[slot].pc && skip < 32) " ++ lb ++ "\n" ++
  "                if (is_unsyncable_csr_read(spike_r.insn) && spike_r.rd != 0) " ++ lb ++ "\n" ++
  "                    uint32_t csr = (spike_r.insn >> 20) & 0xfff;\n" ++
  "                    if (csr == 0xB02 || csr == 0xC02)\n" ++
  "                        spike->set_xreg(spike_r.rd, spike_r.rd_value - 1);\n" ++
  "                " ++ rb ++ "\n" ++
  "                spike_r = spike->step(); skip++; resync_steps++;\n" ++
  "            " ++ rb ++ "\n\n" ++
  "            bool skip_rd_cmp = sync_forced;\n" ++
  "            if (sync_forced) " ++ lb ++ "\n" ++
  "                // After forced PC sync, align Spike's register state with RTL.\n" ++
  "                // Both register files, or an FP value the RTL computed while\n" ++
  "                // Spike was catching up stays stale and every later FP result\n" ++
  "                // is compared against it.\n" ++
  "                if (rvvi[slot].rd_valid) " ++ lb ++ "\n" ++
  "                    if (rvvi[slot].is_fp) spike->set_freg(rvvi[slot].frd, rvvi[slot].frd_data);\n" ++
  "                    else spike->set_xreg(rvvi[slot].rd, rvvi[slot].rd_data);\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n" ++
  "            if (is_unsyncable_csr_read(rvvi[slot].insn) || is_clint_load(rvvi[slot].insn, spike_r.rs1_value)) " ++ lb ++ "\n" ++
  "                if (rvvi[slot].rd_valid && spike_r.rd != 0)\n" ++
  "                    spike->set_xreg(spike_r.rd, rvvi[slot].rd_data);\n" ++
  "                skip_rd_cmp = true;\n" ++
  "            " ++ rb ++ "\n\n" ++
  "            // Golden values from the reference model, one line per retire.\n" ++
  "            if (dump_spike)\n" ++
  "                printf(\"RET pc=%016lx insn=%08x rd=%u rdv=%016lx frd=%u frdv=%016lx fl=%02x\\n\",\n" ++
  "                    (unsigned long)spike_r.pc, spike_r.insn, spike_r.rd,\n" ++
  "                    (unsigned long)spike_r.rd_value, spike_r.frd,\n" ++
  "                    (unsigned long)spike_r.frd_value, (unsigned)spike_r.fflags);\n" ++
  "            if (!sync_forced && rvvi[slot].pc != spike_r.pc) " ++ lb ++ "\n" ++
  "                fprintf(stderr, \"MISMATCH ret#%lu cy%lu slot%d: PC RTL=0x%016lx Spike=0x%016lx (skip %d)\\n\",\n" ++
  "                    retired, cycle, slot, (unsigned long)rvvi[slot].pc, (unsigned long)spike_r.pc, skip);\n" ++
  "                mismatches++;\n" ++
  "            " ++ rb ++ "\n" ++
  "            if (!sync_forced && rvvi[slot].insn != spike_r.insn) " ++ lb ++ "\n" ++
  "                fprintf(stderr, \"MISMATCH ret#%lu cy%lu slot%d: insn RTL=0x%08x Spike=0x%08x\\n\",\n" ++
  "                    retired, cycle, slot, rvvi[slot].insn, spike_r.insn);\n" ++
  "                mismatches++;\n" ++
  "            " ++ rb ++ "\n" ++
  "            if (rvvi[slot].rd_valid && spike_r.rd != 0 && !skip_rd_cmp && !rvvi[slot].is_fp) " ++ lb ++ "\n" ++
  "                if (rvvi[slot].rd_data != spike_r.rd_value) " ++ lb ++ "\n" ++
  "                    fprintf(stderr, \"MISMATCH ret#%lu cy%lu slot%d: PC=0x%016lx insn=0x%08x x%u RTL=0x%016lx Spike=0x%016lx\\n\",\n" ++
  "                        retired, cycle, slot, (unsigned long)rvvi[slot].pc, rvvi[slot].insn, spike_r.rd, (unsigned long)rvvi[slot].rd_data, (unsigned long)spike_r.rd_value);\n" ++
  "                    mismatches++;\n" ++
  "                    {\n" ++
  "                        // What the instruction was given.  Without this an integer\n" ++
  "                        // mismatch names a register and a value and nothing else,\n" ++
  "                        // which is not enough to tell a wrong result from a wrong\n" ++
  "                        // source or from an instruction that should not have run.\n" ++
  "                        unsigned insn = rvvi[slot].insn;\n" ++
  "                        unsigned rs1 = (insn >> 15) & 0x1f, rs2 = (insn >> 20) & 0x1f;\n" ++
  "                        unsigned rd = (insn >> 7) & 0x1f, op = insn & 0x7f;\n" ++
  "                        unsigned f3 = (insn >> 12) & 0x7;\n" ++
  "                        long long imm;\n" ++
  "                        if (op == 0x03 || op == 0x13 || op == 0x67 || op == 0x1b)\n" ++
  "                            imm = (long long)((int)insn >> 20);\n" ++
  "                        else if (op == 0x27)\n" ++
  "                            imm = (long long)((((int)insn >> 25) << 5) | ((insn >> 7) & 0x1f));\n" ++
  "                        else imm = 0;\n" ++
  "                        fprintf(stderr, \"  live rs1 x%u=0x%016lx rs2 x%u=0x%016lx rd x%u=0x%016lx op=0x%02x f3=%u imm=%lld\\n\",\n" ++
  "                            rs1, (unsigned long)spike->get_xreg(rs1), rs2, (unsigned long)spike->get_xreg(rs2),\n" ++
  "                            rd, (unsigned long)spike->get_xreg(rd), op, f3, imm);\n" ++
  "                        // An FP-to-integer conversion reads an FP register, so\n" ++
  "                        // print that operand too.\n" ++
  "                        if (op == 0x53)\n" ++
  "                            fprintf(stderr, \"  fp src f%u hi=0x%016lx lo=0x%016lx rm=%u\\n\",\n" ++
  "                                rs1, (unsigned long)spike->get_freg_hi(rs1), (unsigned long)spike->get_freg(rs1),\n" ++
  "                                (unsigned)((insn >> 12) & 0x7));\n" ++
  "                        fprintf(stderr, \"  wb lsu v=%d tag=%u data=0x%08x | dmem v=%d tag=%u data=0x%08x\\n\",\n" ++
  "                            (int)dut->o_lsu_valid, (unsigned)dut->o_lsu_tag, (unsigned)dut->o_lsu_data,\n" ++
  "                            (int)dut->o_dmem_valid, (unsigned)dut->o_dmem_tag, (unsigned)dut->o_dmem_data);\n" ++
  "                        fprintf(stderr, \"  sb empty=%d full=%d deq_v=%d deq_addr=0x%x load_pend=%d aw_pend=%d\\n\",\n" ++
  "                            (int)dut->o_sb_empty, (int)dut->o_sb_full, (int)dut->o_sb_deq_v, (unsigned)dut->o_sb_cnt,\n" ++
  "                            (int)dut->o_load_pending, (int)dut->o_aw_pend);\n" ++
  "                        " ++ lb ++ "\n" ++
  "                            int shown = 0;\n" ++
  "                            for (unsigned wa = 0; wa < MEM_SIZE_WORDS && shown < 6; wa++) " ++ lb ++ "\n" ++
  "                                unsigned rv = (unsigned)rtl_shadow[wa*4] | ((unsigned)rtl_shadow[wa*4+1] << 8)\n" ++
  "                                             | ((unsigned)rtl_shadow[wa*4+2] << 16) | ((unsigned)rtl_shadow[wa*4+3] << 24);\n" ++
  "                                unsigned sv = spike->read_mem(wa*4);\n" ++
  "                                if (rv != sv) " ++ lb ++ "\n" ++
  "                                    fprintf(stderr, \"  SHADOW addr=0x%05x rtl=0x%08x spike=0x%08x\\n\", wa*4, rv, sv);\n" ++
  "                                    for (unsigned wi = 0; wi < wr_n && wi < 64; wi++) " ++ lb ++ "\n" ++
  "                                        WRec &w = wr_ring[(wr_n - 1 - wi) % 64];\n" ++
  "                                        if ((w.addr & ~3u) == wa*4) " ++ lb ++ "\n" ++
  "                                            fprintf(stderr, \"    wrote cy%u addr=0x%x data=0x%llx sz=%u\\n\", w.cy, w.addr, w.data, w.sz);\n" ++
  "                                        " ++ rb ++ "\n" ++
  "                                    " ++ rb ++ "\n" ++
  "                                    shown++;\n" ++
  "                                " ++ rb ++ "\n" ++
  "                            " ++ rb ++ "\n" ++
  "                        " ++ rb ++ "\n" ++
  "                        " ++ lb ++ "\n" ++
  "                            int first = wb_n > WB_RING ? wb_n - WB_RING : 0;\n" ++
  "                            fprintf(stderr, \"  wb ring:\");\n" ++
  "                            for (int wi = first; wi < wb_n; wi++) " ++ lb ++ "\n" ++
  "                                WbRec &r = wb_ring[wi % WB_RING];\n" ++
  "                                fprintf(stderr, \" [cy%u %s tag%u=0x%llx]\", r.cy, r.lane ? \"dmem\" : \"lsu\", r.tag, r.data);\n" ++
  "                            " ++ rb ++ "\n" ++
  "                            fprintf(stderr, \"\\n\");\n" ++
  "                            int rf = req_n > WB_RING ? req_n - WB_RING : 0;\n" ++
  "                            fprintf(stderr, \"  req ring:\");\n" ++
  "                            for (int ri = rf; ri < req_n; ri++) " ++ lb ++ "\n" ++
  "                                ReqRec &q = req_ring[ri % WB_RING];\n" ++
  "                                fprintf(stderr, \" [cy%u v=%u we=%u aw=%u a=0x%x]\", q.cy, q.v, q.we, q.aw, q.addr);\n" ++
  "                            " ++ rb ++ "\n" ++
  "                            fprintf(stderr, \"\\n\");\n" ++
  "                            unsigned wf = wr_n > 16 ? wr_n - 16 : 0;\n" ++
  "                            fprintf(stderr, \"  wr ring:\");\n" ++
  "                            for (unsigned wi = wf; wi < wr_n; wi++) " ++ lb ++ "\n" ++
  "                                WRec &w = wr_ring[wi % 64];\n" ++
  "                                fprintf(stderr, \" [cy%u a=0x%x d=0x%llx sz=%u]\", w.cy, w.addr, w.data, w.sz);\n" ++
  "                            " ++ rb ++ "\n" ++
  "                            fprintf(stderr, \"\\n\");\n" ++
  "                        " ++ rb ++ "\n" ++

  "                        if (op == 0x53 || (op >= 0x43 && op <= 0x4f))\n" ++
  "                            fprintf(stderr, \"  live f%u=0x%016lx hi=0x%016lx f%u=0x%016lx hi=0x%016lx\\n\",\n" ++
  "                                rs1, (unsigned long)spike->get_freg(rs1), (unsigned long)spike->get_freg_hi(rs1),\n" ++
  "                                rs2, (unsigned long)spike->get_freg(rs2), (unsigned long)spike->get_freg_hi(rs2));\n" ++
  "                        if (op == 0x03 || op == 0x27 || op == 0x23 || op == 0x2f) {\n" ++
  "                            unsigned long addr = (unsigned long)(spike->get_xreg(rs1) + (unsigned long long)imm) & ~0x3UL;\n" ++
  "                            fprintf(stderr, \"  mem[0x%lx] rtl=0x%08x spike=0x%08x\\n\",\n" ++
  "                                addr, dpi_mem_read((unsigned)(addr >> 2)), spike->read_mem(addr));\n" ++
  "                        }\n" ++
  "                    }\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n" ++
  "            // FP destination: the value lives in the FP register file.\n" ++
  "            // After a resync the two states were force-aligned, so a\n" ++
  "            // difference here says nothing; skip it like the integer side.\n" ++
  "            if (rvvi[slot].is_fp && spike_r.frd_valid && !skip_rd_cmp) " ++ lb ++ "\n" ++
  "                if (rvvi[slot].frd_data != spike_r.frd_value) " ++ lb ++ "\n" ++
  "                    if (fp_mismatch_prints++ < 16) " ++ lb ++ "\n" ++
  "                    fprintf(stderr, \"MISMATCH ret#%lu cy%lu slot%d: PC=0x%016lx insn=0x%08x f%u RTL=0x%016lx Spike=0x%016lx fs1=0x%016lx fs2=0x%016lx fs3=0x%016lx mstatus=0x%lx fcsr=0x%lx\\n\",\n" ++
  "                        retired, cycle, slot, (unsigned long)rvvi[slot].pc, rvvi[slot].insn, spike_r.frd, (unsigned long)rvvi[slot].frd_data, (unsigned long)spike_r.frd_value,\n" ++
  "                        (unsigned long)spike_r.fs1_value, (unsigned long)spike_r.fs2_value, (unsigned long)spike_r.fs3_value,\n" ++
  "                        (unsigned long)spike->get_csr(0x300), (unsigned long)spike->get_csr(0x003));\n" ++
  "                    fprintf(stderr, \"  live rd=f%u:0x%016lx rs1=f%u:0x%016lx rs2=f%u:0x%016lx hi_rd=0x%016lx hi_rs1=0x%016lx\\n\",\n" ++
  "                        (unsigned)((rvvi[slot].insn >> 7) & 0x1f), (unsigned long)spike->get_freg((rvvi[slot].insn >> 7) & 0x1f),\n" ++
  "                        (unsigned)((rvvi[slot].insn >> 15) & 0x1f), (unsigned long)spike->get_freg((rvvi[slot].insn >> 15) & 0x1f),\n" ++
  "                        (unsigned)((rvvi[slot].insn >> 20) & 0x1f), (unsigned long)spike->get_freg((rvvi[slot].insn >> 20) & 0x1f),\n" ++
  "                        (unsigned long)spike->get_freg_hi((rvvi[slot].insn >> 7) & 0x1f),\n" ++
  "                        (unsigned long)spike->get_freg_hi((rvvi[slot].insn >> 15) & 0x1f));\n" ++
  "                    " ++ rb ++ "\n" ++
  "                    mismatches++;\n" ++
  "                " ++ rb ++ "\n" ++
  "            " ++ rb ++ "\n\n" ++
  "            // FP exception flags.  The RTL accumulates them at commit and Spike\n" ++
  "            // at execute, so a transient difference is possible; keep them in a\n" ++
  "            // separate counter so the two classes stay distinguishable.\n" ++
  "            if (!skip_rd_cmp && (slot == 0 ? dut->o_rvvi_fflags_0 : dut->o_rvvi_fflags_slot1) != spike_r.fflags) " ++ lb ++ "\n" ++
  "                if (fflag_mismatches < 8)\n" ++
  "                    fprintf(stderr, \"FFLAG ret#%lu cy%lu slot%d: PC=0x%016lx insn=0x%08x RTL=0x%02x Spike=0x%02x\\n\",\n" ++
  "                        retired, cycle, slot, (unsigned long)rvvi[slot].pc, rvvi[slot].insn, (unsigned)(slot == 0 ? dut->o_rvvi_fflags_0 : dut->o_rvvi_fflags_slot1), (unsigned)spike_r.fflags);\n" ++
  "                fflag_mismatches++;\n" ++
  "            " ++ rb ++ "\n\n" ++
  "            last_pc = rvvi[slot].pc;\n" ++
  "            last_insn = rvvi[slot].insn;\n" ++
  "            retired++;\n" ++
  "            if (mismatches > 200) " ++ lb ++ " fprintf(stderr, \"Too many mismatches\\n\"); done = true; break; " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        // Memory comparison.  A store writes no register, so the register\n" ++
  "        // comparison above cannot see a store bug; it surfaces much later as\n" ++
  "        // a load mismatch with no pointer to the offending store.  The\n" ++
  "        // harness counts the words it writes; when that count moves, watch\n" ++
  "        // those words against the reference model.  A word that differs\n" ++
  "        // only while a store drains is dropped; one that stays different is\n" ++
  "        // reported with the store that wrote it.\n" ++
  "        unsigned int wr_count = dpi_mem_wr_count();\n" ++
  "        if (wr_count != last_wr_count) " ++ lb ++ "\n" ++
  "            last_wr_count = wr_count;\n" ++
  "            unsigned int base = dpi_mem_wr_idx();\n" ++
  "            unsigned int words = dpi_mem_wr_words();\n" ++
  "            for (unsigned int w = 0; w < words && pending_addr == MEM_NO_PENDING; w++) " ++ lb ++ "\n" ++
  "                if (base + w >= MEM_SIZE_WORDS) continue;  // MMIO, not RAM\n" ++
  "                if (dpi_mem_read(base + w) == spike->read_mem((uint64_t)(base + w) * 4)) continue;\n" ++
  "                pending_addr = base + w;\n" ++
  "                pending_age  = 0;\n" ++
  "            " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n" ++
  "        if (pending_addr != MEM_NO_PENDING) " ++ lb ++ "\n" ++
  "            uint32_t rtl_word = dpi_mem_read(pending_addr);\n" ++
  "            uint32_t spike_word = spike->read_mem((uint64_t)pending_addr * 4);\n" ++
  "            if (rtl_word == spike_word) " ++ lb ++ "\n" ++
  "                pending_addr = MEM_NO_PENDING;\n" ++
  "            " ++ rb ++ " else if (++pending_age >= MEM_PERSIST_CYCLES) " ++ lb ++ "\n" ++
  "                mem_mismatches++;\n" ++
  "                if (mem_mismatches <= 16)\n" ++
  "                    fprintf(stderr, \"MEMSTORE ret#%lu cy%lu addr=0x%08x RTL=0x%08x Spike=0x%08x resync=%lu\\n\",\n" ++
  "                        retired, cycle, pending_addr * 4, rtl_word, spike_word, resync_steps);\n" ++
  "                pending_addr = MEM_NO_PENDING;\n" ++
  "            " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        // Watched word: report every change on either side, with the\n" ++
  "        // instruction retiring when it happened.  That names the store that\n" ++
  "        // wrote it and the store that should have.\n" ++
  "        if (watch_en && watch_addr / 4 < MEM_SIZE_WORDS) " ++ lb ++ "\n" ++
  "            uint32_t rtl_word = dpi_mem_read((unsigned int)(watch_addr / 4));\n" ++
  "            uint32_t spike_word = spike->read_mem(watch_addr);\n" ++
  "            bool changed = (rtl_word != watch_rtl_prev) || (spike_word != watch_spike_prev);\n" ++
  "            if (changed && watch_reports < 40) " ++ lb ++ "\n" ++
  "                fprintf(stderr, \"MEMWATCH ret#%lu cy%lu addr=0x%08lx RTL=0x%08x (was 0x%08x) Spike=0x%08x (was 0x%08x) pc=0x%lx insn=0x%08x\\n\",\n" ++
  "                    retired, cycle, (unsigned long)watch_addr, rtl_word, watch_rtl_prev,\n" ++
  "                    spike_word, watch_spike_prev, (unsigned long)last_pc, last_insn);\n" ++
  "                watch_reports++;\n" ++
  "            " ++ rb ++ "\n" ++
  "            watch_rtl_prev = rtl_word;\n" ++
  "            watch_spike_prev = spike_word;\n" ++
  "        " ++ rb ++ "\n\n" ++
  "        // Every writeback broadcast, kept as a ring.  A mismatch names the value\n" ++
  "        // that reached a register but not where it came from; this does.\n" ++
  "        // Every atomic write request, so a missing one is visible.\n" ++
  "        if (dut->o_aw_pending || dut->o_dmem_req_v) " ++ lb ++ "\n" ++
  "            ReqRec &q = req_ring[req_n % WB_RING];\n" ++
  "            q.cy = (unsigned)cycle; q.aw = dut->o_aw_pending;\n" ++
  "            q.we = dut->o_dmem_we; q.v = dut->o_dmem_req_v; q.addr = dut->o_mem_req_addr;\n" ++
  "            req_n++;\n" ++
  "        " ++ rb ++ "\n" ++
  "        // Only architectural writes: a store-buffer drain or the atomic\'s own\n" ++
  "        // read-modify-write.  A cache eviction also drives this port, and its\n" ++
  "        // data is a line, not the word the program stored.\n" ++
  "        if (dut->o_dmem_req_v && dut->o_dmem_we && (dut->o_sb_deq_v || dut->o_aw_pending)) " ++ lb ++ "\n" ++
  "            // The request address is a byte address: a halfword at offset 2\n" ++
  "            // belongs at offset 2, not at the word base.\n" ++
  "            unsigned n = 1u << dut->o_req_size, a0 = dut->o_req_addr;\n" ++
  "            unsigned long long dw = (unsigned long long)dut->o_req_data;\n" ++
  "            for (unsigned b = 0; b < n && a0 + b < sizeof(rtl_shadow); b++)\n" ++
  "                rtl_shadow[a0 + b] = (unsigned char)((dw >> (8 * b)) & 0xff);\n" ++
  "            wr_ring[wr_n % 64].cy = (unsigned)cycle; wr_ring[wr_n % 64].addr = a0;\n" ++
  "            wr_ring[wr_n % 64].data = dw; wr_ring[wr_n % 64].sz = dut->o_req_size;\n" ++
  "            wr_n++;\n" ++
  "        " ++ rb ++ "\n" ++
  "        // Every accepted load response must equal the word the architecture\n" ++
  "        // says is there.  A cache between the core and memory can answer from a\n" ++
  "        // stale line, and the register comparison reports only the value, not\n" ++
  "        // the address it should have had.\n" ++
  "        if (dut->o_dmem_valid && load_bad < 12) " ++ lb ++ "\n" ++
  "            unsigned la = (unsigned)dut->o_load_addr;\n" ++
  "            unsigned lb_n = 1u << dut->o_load_size;\n" ++
  "            unsigned long long got = (unsigned long long)dut->o_dmem_data;\n" ++
  "            int bad = 0;\n" ++
  "            for (unsigned b = 0; b < lb_n && la + b < sizeof(rtl_shadow); b++)\n" ++
  "                if ((unsigned char)(got >> (8*b)) != rtl_shadow[la + b]) bad = 1;\n" ++
  "            if (bad) " ++ lb ++ "\n" ++
  "                fprintf(stderr, \"  LOADBAD cy%llu addr=0x%x size=%u got=0x%llx want=0x%02x%02x%02x%02x%02x%02x%02x%02x\\n\",\n" ++
  "                    (unsigned long long)cycle, la, (unsigned)dut->o_load_size, got,\n" ++
  "                    rtl_shadow[la+7], rtl_shadow[la+6], rtl_shadow[la+5], rtl_shadow[la+4],\n" ++
  "                    rtl_shadow[la+3], rtl_shadow[la+2], rtl_shadow[la+1], rtl_shadow[la+0]);\n" ++
  "                load_bad++;\n" ++
  "            " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n" ++
  "        if (dut->o_lsu_valid || dut->o_dmem_valid) " ++ lb ++ "\n" ++
  "            WbRec &r = wb_ring[wb_n % WB_RING];\n" ++
  "            r.cy = (unsigned)cycle;\n" ++
  "            r.lane = dut->o_lsu_valid ? 0 : 1;\n" ++
  "            r.tag = dut->o_lsu_valid ? dut->o_lsu_tag : dut->o_dmem_tag;\n" ++
  "            r.data = dut->o_lsu_valid ? dut->o_lsu_data : dut->o_dmem_data;\n" ++
  "            wb_n++;\n" ++
  "        " ++ rb ++ "\n" ++
  "        if (dut->o_test_done) done = true;\n" ++
  "        dut->clk = 0; dut->eval();\n" ++
  "        cycle++;\n" ++
  "        spike->tick_timer();\n" ++
  "    " ++ rb ++ "\n\n" ++
  "    // Full-memory diff on request: walk both memories and print every word\n" ++
  "    // that differs, which bounds where a store went wrong.\n" ++
  "    if (mem_diff_dump) " ++ lb ++ "\n" ++
  "        unsigned long diffs = 0, shown = 0;\n" ++
  "        for (unsigned int i = 0; i < MEM_SIZE_WORDS; i++) " ++ lb ++ "\n" ++
  "            uint32_t rtl_word = dpi_mem_read(i);\n" ++
  "            uint32_t spike_word = spike->read_mem((uint64_t)i * 4);\n" ++
  "            if (rtl_word == spike_word) continue;\n" ++
  "            diffs++;\n" ++
  "            if (shown < 32) " ++ lb ++ "\n" ++
  "                printf(\"MEMDIFF addr=0x%08x RTL=0x%08x Spike=0x%08x\\n\", i * 4, rtl_word, spike_word);\n" ++
  "                shown++;\n" ++
  "            " ++ rb ++ "\n" ++
  "        " ++ rb ++ "\n" ++
  "        printf(\"  Mem words differing: %lu\\n\", diffs);\n" ++
  "    " ++ rb ++ "\n\n" ++
  "    printf(\"Cosimulation complete:\\n\");\n" ++
  "    printf(\"  Cycles:      %lu\\n\", cycle);\n" ++
  "    printf(\"  Retired:     %lu\\n\", retired);\n" ++
  "    printf(\"  IPC:         %.3f\\n\", cycle > 0 ? (double)retired / cycle : 0.0);\n" ++
  "    printf(\"  Mismatches:  %lu\\n\", mismatches);\n" ++
  "    printf(\"  FFLAG diff:  %lu\\n\", fflag_mismatches);\n" ++
  "    printf(\"  Mem store diff: %lu\\n\", mem_mismatches);\n" ++
  "    printf(\"  Resync steps: %lu\\n\", resync_steps);\n" ++
  "    printf(\"  tohost:      0x%08x\\n\", dut->o_tohost);\n" ++
  "    printf(\"  Spike PC:    0x%016lx\\n\", (unsigned long)spike->get_pc());\n" ++
  "    printf(\"  rob_empty:   %d\\n\", (int)dut->o_rob_empty);\n" ++
  "    printf(\"  head_ready:  %d  fp_eu_busy: %d  div_busy: %d  fp_busy: 0x%016lx\\n\",\n" ++
  "        (int)dut->o_commit_ready, (int)dut->o_fp_busy_eu, (int)dut->o_div_busy,\n" ++
  "        (unsigned long)dut->o_fp_busy);\n" ++
  "    printf(\"  rtl pc:      0x%08x slot0 0x%08x slot1\\n\",\n" ++
  "        (unsigned)dut->o_rvvi_pc_rdata_0, (unsigned)dut->o_rvvi_pc_rdata_1);\n" ++
  "    printf(\"  fp issue: dest=%u s1=%u(%d ready) s2=%u(%d ready) disp_en=%d\\n\",\n" ++
  "        (unsigned)dut->o_fp_dest_tag, (unsigned)dut->o_fp_s1_tag, (int)dut->o_fp_s1_ready,\n" ++
  "        (unsigned)dut->o_fp_s2_tag, (int)dut->o_fp_s2_ready, (int)dut->o_fp_dispatch_en);\n" ++
  "    printf(\"  fp station: avail=%d disp_valid=%d flush=%d\\n\",\n" ++
  "        (int)dut->o_fp_avail, (int)dut->o_fp_disp_valid, (int)dut->o_flush_rs_fp);\n" ++
  "    printf(\"  rename: fp_disp_pre=%d fp_ren_valid=%d disp_stall=%d ext_stall=%d supp_stall=%d rob_full=%d\\n\",\n" ++
  "        (int)dut->o_fp_disp_pre, (int)dut->o_fp_ren_valid, (int)dut->o_dispatch_stall,\n" ++
  "        (int)dut->o_rename_ext_stall, (int)dut->o_rename_supp_stall, (int)dut->o_rob_full);\n" ++
  "    printf(\"  probe2: hw_suppress=%d useq_active=%d fallback_active=%d stall_req_im=%d stall_req_bm=%d fp_stall_req_0=%d sb_stall_req_0=%d suppress_pre=%d\\n\", (int)dut->o_hw_suppress, (int)dut->o_useq_active, (int)dut->o_fallback_active, (int)dut->o_stall_req_im, (int)dut->o_stall_req_bm, (int)dut->o_fp_stall_req_0, (int)dut->o_sb_stall_req_0, (int)dut->o_suppress_pre);\n" ++
  "    printf(\"  probe3: lsu_sb_full=%d lsu_sb_flush_pending=%d fi_start_nocsr=%d fence_i_draining=%d d0_needs_sb=%d\\n\", (int)dut->o_lsu_sb_full, (int)dut->o_lsu_sb_flush_pending, (int)dut->o_fi_start_nocsr, (int)dut->o_fence_i_draining, (int)dut->o_d0_needs_sb);\n" ++
  "    printf(\"  probe4: rob_empty=%d hw_draining_reg=%d fence_start_delayed=%d\\n\", (int)dut->o_rob_empty, (int)dut->o_hw_draining_reg, (int)dut->o_fence_start_delayed);\n" ++
  "    printf(\"  probe4: rob_empty=%d\\n\", (int)dut->o_rob_empty);\n" ++
  "    printf(\"  probe5: lsu_sb_empty=%d lsu_sb_deq_valid=%d commit_store_en=%d\\n\", (int)dut->o_lsu_sb_empty, (int)dut->o_lsu_sb_deq_valid, (int)dut->o_commit_store_en);\n" ++
  "    printf(\"  dbg_sb=0x%016llx dbg_amo=0x%08llx\\n\", (unsigned long long)dut->o_dbg_sb, (unsigned long long)dut->o_dbg_amo);\n" ++
  "    printf(\"  probe6: rs_e0_valid=%d rs_e1_valid=%d rs_e0_ready=%d rs_e1_ready=%d\\n\", (int)dut->o_rs_e0_valid, (int)dut->o_rs_e1_valid, (int)dut->o_rs_e0_ready, (int)dut->o_rs_e1_ready);\n" ++
  "    printf(\"  probe7: d0_base_tmp=%d d0_base_pre=%d\\n\", (int)dut->o_d0_base_tmp, (int)dut->o_d0_base_pre);\n" ++
  "    printf(\"  probe8: cdb_inj=%d all_inj=%d cdb_fp_valid=%d fb_active=%d\\n\", (int)dut->o_fallback_cdb_inject, (int)dut->o_all_cdb_inject, (int)dut->o_cdb_valid_fp_prf, (int)dut->o_fallback_active);\n" ++
  "    printf(\"  probe9: fp_drain_mode=%d fp_stale_suppress=%d fp_valid_out=%d fp_enq_valid_gated=%d fp_drain_hold=%d\\n\", (int)dut->o_fp_drain_mode, (int)dut->o_fp_stale_suppress, (int)dut->o_fp_valid_out, (int)dut->o_fp_enq_valid_gated, (int)dut->o_fp_drain_hold);\n" ++
  "    printf(\"  probe: fence_i_suppress=%dcsr_rename_en=%dsuppress_all=%dtrap_or_mret_det=%dstall_rr=%dstall_req_rs0=%dredirect_or=%dpipeline_flush=%ddmem_stall_ext=%dfetch_stall_ext=%d\\n\", (int)dut->o_fence_i_suppress, (int)dut->o_csr_rename_en, (int)dut->o_suppress_all, (int)dut->o_trap_or_mret_det, (int)dut->o_stall_rr, (int)dut->o_stall_req_rs0, (int)dut->o_redirect_or, (int)dut->o_pipeline_flush, (int)dut->o_dmem_stall_ext, (int)dut->o_fetch_stall_ext);\n\n" ++
  "    if (dut->o_tohost == 1 && mismatches == 0)\n" ++
  "        printf(\"COSIM PASS\\n\");\n" ++
  "    else\n" ++
  "        printf(\"COSIM FAIL\\n\");\n\n" ++
  "    if (g_cosim_uart_tx_file) { fclose(g_cosim_uart_tx_file); g_cosim_uart_tx_file = nullptr; }\n" ++
  "    return (dut->o_tohost == 1 && mismatches == 0) ? 0 : 1;\n" ++
  rb ++ "\n"

/-! ## File Writers -/

def testbenchOutputDir : String := "testbench/generated"

def writeTestbenchSV (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let sv := if cfg.cacheLineMemPort.isSome then toTestbenchSVCached cfg else toTestbenchSV cfg
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let path := s!"{testbenchOutputDir}/{tbName}.sv"
  IO.FS.writeFile path sv
  IO.println s!"  ✓ {tbName}.sv (testbench)"

def writeCpuSetup (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let c := cfg.circuit
  -- Thin setup header (port order + names only)
  IO.FS.writeFile s!"{testbenchOutputDir}/cpu_setup_{c.name}.h" (toCpuSetupHeader c)
  -- Heavy setup cpp (includes full module header)
  IO.FS.writeFile s!"{testbenchOutputDir}/cpu_setup_{c.name}.cpp" (toCpuSetupCpp cfg)

def writeTestbenchCppSim (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let c := cfg.circuit
  Testbench.writeCpuSetup cfg
  -- Write thin sim_main (no module header includes)
  let sc := toTestbenchCppSim cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/sim_main_{c.name}.cpp" sc
  IO.println s!"  ✓ sim_main_{c.name}.cpp + cpu_setup_{c.name}.cpp (testbench, split)"

def writeSimMainCpp (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let cpp := toSimMainCpp cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/sim_main_{tbName}.cpp" cpp
  IO.println s!"  ✓ sim_main_{tbName}.cpp (Verilator sim driver)"

def writeCosimMainCpp (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let cpp := toCosimMainCpp cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/cosim_main_{tbName}.cpp" cpp
  IO.println s!"  ✓ cosim_main_{tbName}.cpp (Verilator cosim driver)"

def writeLeanSim (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let c := cfg.circuit
  let h := toLeanSimH cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/lean_sim_{c.name}.h" h
  let cpp := toLeanSimCpp cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/lean_sim_{c.name}.cpp" cpp
  IO.println s!"  ✓ lean_sim_{c.name}.h + lean_sim_{c.name}.cpp (Lean gate-level sim)"

def writeLeanSimMainCpp (cfg : TestbenchConfig) : IO Unit := do
  IO.FS.createDirAll testbenchOutputDir
  let tbName := optOrDefault cfg.tbName s!"tb_{cfg.circuit.name}"
  let cpp := toLeanSimMainCpp cfg
  IO.FS.writeFile s!"{testbenchOutputDir}/lean_sim_main_{tbName}.cpp" cpp
  IO.println s!"  ✓ lean_sim_main_{tbName}.cpp (Lean simulator driver)"

def writeTestbenches (cfg : TestbenchConfig) : IO Unit := do
  Testbench.writeTestbenchSV cfg
  -- CppSim (plain C++ model) does not support the cache-line memory interface;
  -- LeanSim does, so the gate-level model + its standalone driver are always
  -- emitted (bench-cppsim builds from them).
  if cfg.cacheLineMemPort.isNone then
    Testbench.writeTestbenchCppSim cfg
  Testbench.writeCpuSetup cfg
  Testbench.writeLeanSim cfg
  Testbench.writeSimMainCpp cfg
  Testbench.writeLeanSimMainCpp cfg
  Testbench.writeCosimMainCpp cfg

end Shoumei.Codegen.Testbench
