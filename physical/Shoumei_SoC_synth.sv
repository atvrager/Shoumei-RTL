// Synthesis wrapper for Shoumei_SoC
// Full System-on-Chip: Shoumei RV64 OoO CPU + Caches + Interconnect + Peripherals (UART, GPIO, ACLINT, APLIC, BootROM, SRAM)
// Clean pinout for ASIC pad ring and external DRAM / bus integration.

module Shoumei_SoC_synth (
  input  logic          clock,
  input  logic          reset_n,
  // External UART
  input  logic          uart_rx,
  output logic          uart_tx,
  // External GPIO
  input  logic [7:0]    gpio_i,
  output logic [7:0]    gpio_o,
  output logic [7:0]    gpio_oen,
  // Main memory interface (to external DRAM / AXI bridge)
  input  logic          mem_resp_valid,
  input  logic [255:0]  mem_resp_data,
  output logic          mem_req_valid,
  output logic [31:0]   mem_req_addr,
  output logic          mem_req_we,
  output logic [255:0]  mem_req_data,
  // Status
  output logic          rob_empty
);

  Shoumei_SoC u_soc (
    .clock(clock),
    .reset_n(reset_n),
    .uart_rx(uart_rx),
    .uart_tx(uart_tx),
    .gpio_i(gpio_i),
    .gpio_o(gpio_o),
    .gpio_oen(gpio_oen),
    .mem_resp_valid(mem_resp_valid),
    .mem_resp_data(mem_resp_data),
    .mem_req_valid(mem_req_valid),
    .mem_req_addr(mem_req_addr),
    .mem_req_we(mem_req_we),
    .mem_req_data(mem_req_data),
    .rob_empty(rob_empty)
  );

endmodule
