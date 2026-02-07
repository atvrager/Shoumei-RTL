//==============================================================================
// tb_cpu.sv - Top-level CPU testbench
//
// Wraps the CPU_RV32IM module with:
//   - Instruction memory (combinational read, word-addressed)
//   - Data memory (1-cycle latency, word-addressed)
//   - HTIF tohost/fromhost termination protocol
//   - Cycle counter and timeout
//
// Memory map:
//   0x00000000 - 0x0000FFFF : Instruction memory (64KB)
//   0x00000000 - 0x0000FFFF : Data memory (shared, 64KB)
//   0x00001000              : tohost (write 1 = PASS, else FAIL)
//
// Usage:
//   Load program into imem/dmem via $readmemh or Verilator C++ harness.
//   Assert reset for >=4 cycles, then release.
//   Simulation terminates on tohost write or cycle timeout.
//==============================================================================

module tb_cpu #(
    parameter MEM_SIZE_WORDS = 16384,   // 64KB / 4 = 16K words
    parameter TIMEOUT_CYCLES = 100000,
    parameter TOHOST_ADDR    = 32'h00001000
) (
    input logic clk,
    input logic rst_n,
    // Exposed for C++ harness
    output logic        o_test_done,
    output logic        o_test_pass,
    output logic [31:0] o_test_code,
    output logic [31:0] o_fetch_pc,
    output logic        o_rob_empty,
    output logic        o_global_stall,
    output logic [31:0] o_cycle_count
);

  // =========================================================================
  // CPU I/O signals
  // =========================================================================
  logic        reset;
  logic [31:0] imem_resp_data;
  logic        dmem_req_ready;
  logic        dmem_resp_valid;
  logic [31:0] dmem_resp_data;
  logic [31:0] branch_redirect_target;

  logic [31:0] fetch_pc;
  logic        fetch_stalled;
  logic        global_stall_out;
  logic        dmem_req_valid;
  logic        dmem_req_we;
  logic [31:0] dmem_req_addr;
  logic [31:0] dmem_req_data;
  logic        rob_empty;

  assign reset = ~rst_n;

  // No branch redirect for now
  assign branch_redirect_target = 32'b0;

  // =========================================================================
  // CPU instance
  // =========================================================================
  CPU_RV32IM u_cpu (
      .clock                  (clk),
      .reset                  (reset),
      .zero                   (1'b0),
      .one                    (1'b1),
      .imem_resp_data         (imem_resp_data),
      .dmem_req_ready         (dmem_req_ready),
      .dmem_resp_valid        (dmem_resp_valid),
      .dmem_resp_data         (dmem_resp_data),
      .branch_redirect_target (branch_redirect_target),
      .fetch_pc               (fetch_pc),
      .fetch_stalled          (fetch_stalled),
      .global_stall_out       (global_stall_out),
      .dmem_req_valid         (dmem_req_valid),
      .dmem_req_we            (dmem_req_we),
      .dmem_req_addr          (dmem_req_addr),
      .dmem_req_data          (dmem_req_data),
      .rob_empty              (rob_empty)
  );

  // =========================================================================
  // Memory: shared instruction + data, word-addressed
  // =========================================================================
  logic [31:0] mem [0:MEM_SIZE_WORDS-1] /* verilator public */;

  // Base address for memory mapping (word offset)
  localparam logic [31:0] MEM_BASE = 32'h00000000;

  function automatic logic [31:0] addr_to_idx(input logic [31:0] addr);
    return (addr - MEM_BASE) >> 2;
  endfunction

  // --- Instruction memory: combinational read ---
  assign imem_resp_data = mem[addr_to_idx(fetch_pc)];

  // --- Data memory: 1-cycle latency ---
  logic        dmem_pending;
  logic [31:0] dmem_read_data;

  assign dmem_req_ready = 1'b1;  // Always ready

  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      dmem_resp_valid <= 1'b0;
      dmem_read_data  <= 32'b0;
      dmem_pending    <= 1'b0;
    end else begin
      dmem_pending    <= 1'b0;
      dmem_resp_valid <= 1'b0;

      if (dmem_req_valid) begin
        if (dmem_req_we) begin
          // Store
          mem[addr_to_idx(dmem_req_addr)] <= dmem_req_data;
        end else begin
          // Load: respond next cycle
          dmem_read_data  <= mem[addr_to_idx(dmem_req_addr)];
          dmem_pending    <= 1'b1;
        end
      end

      if (dmem_pending) begin
        dmem_resp_valid <= 1'b1;
      end
    end
  end

  assign dmem_resp_data = dmem_read_data;

  // =========================================================================
  // HTIF: tohost termination
  // =========================================================================
  logic        test_done;
  logic        test_pass;
  logic [31:0] test_code;

  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      test_done <= 1'b0;
      test_pass <= 1'b0;
      test_code <= 32'b0;
    end else begin
      // Watch for stores to tohost address
      if (dmem_req_valid && dmem_req_we &&
          dmem_req_addr == TOHOST_ADDR) begin
        test_done <= 1'b1;
        test_code <= dmem_req_data;
        test_pass <= (dmem_req_data == 32'h1);
      end
    end
  end

  // =========================================================================
  // Cycle counter and timeout
  // =========================================================================
  logic [31:0] cycle_count;

  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      cycle_count <= 32'b0;
    end else begin
      cycle_count <= cycle_count + 1;
    end
  end

  // =========================================================================
  // Simulation control (for Verilator / simulator)
  // =========================================================================

  // These signals are read by the C++ harness
  // test_done, test_pass, test_code, cycle_count, fetch_pc, rob_empty

  // Trace output for debugging (enable with +define+TRACE_RETIRE)
  `ifdef TRACE_RETIRE
  always_ff @(posedge clk) begin
    if (!reset) begin
      $display("[cycle %0d] PC=0x%08h stall=%b rob_empty=%b cdb_valid=%b commit=%b",
               cycle_count, fetch_pc, global_stall_out, rob_empty,
               u_cpu.cdb_valid, u_cpu.rob_commit_en);
    end
  end
  `endif

  // Expose internal signals to C++ harness
  assign o_test_done    = test_done;
  assign o_test_pass    = test_pass;
  assign o_test_code    = test_code;
  assign o_fetch_pc     = fetch_pc;
  assign o_rob_empty    = rob_empty;
  assign o_global_stall = global_stall_out;
  assign o_cycle_count  = cycle_count;

endmodule
