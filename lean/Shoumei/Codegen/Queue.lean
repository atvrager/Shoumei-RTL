/-
Codegen/Queue.lean - Code Generation for Queue Circuits

Generates SystemVerilog and Chisel from QueueCircuit structures.
-/

import Shoumei.Circuits.Sequential.Queue

namespace Shoumei.Codegen.Queue

open Shoumei.Circuits.Sequential

/-!
## Queue Code Generation

Generates ready/valid handshaking hardware from QueueCircuit specifications.
-/

-- Generate SystemVerilog for a Queue
def toSystemVerilog (q : QueueCircuit) : String :=
  let moduleName := q.name
  let width := q.width
  let widthMinus1 := width - 1

  s!"module {moduleName}(\n" ++
  s!"  input  wire [{widthMinus1}:0] enq_data,\n" ++
  s!"  input  wire              enq_valid,\n" ++
  s!"  output reg               enq_ready,\n" ++
  s!"  output reg  [{widthMinus1}:0] deq_data,\n" ++
  s!"  output reg               deq_valid,\n" ++
  s!"  input  wire              deq_ready,\n" ++
  s!"  input  wire              clock,\n" ++
  s!"  input  wire              reset\n" ++
  s!");\n" ++
  s!"\n" ++
  s!"  // State: valid bit and data storage\n" ++
  s!"  reg valid;\n" ++
  s!"  reg [{widthMinus1}:0] data;\n" ++
  s!"\n" ++
  s!"  // Combinational outputs\n" ++
  s!"  always @(*) begin\n" ++
  s!"    enq_ready = !valid;\n" ++
  s!"    deq_valid = valid;\n" ++
  s!"    deq_data = data;\n" ++
  s!"  end\n" ++
  s!"\n" ++
  s!"  // Sequential logic\n" ++
  s!"  always @(posedge clock) begin\n" ++
  s!"    if (reset) begin\n" ++
  s!"      valid <= 1'b0;\n" ++
  s!"      data <= {width}'d0;\n" ++
  s!"    end else begin\n" ++
  s!"      // Simultaneous enq and deq: flow through\n" ++
  s!"      if (enq_valid && enq_ready && deq_valid && deq_ready) begin\n" ++
  s!"        data <= enq_data;\n" ++
  s!"        valid <= 1'b1;\n" ++
  s!"      end\n" ++
  s!"      // Only enqueue\n" ++
  s!"      else if (enq_valid && enq_ready) begin\n" ++
  s!"        data <= enq_data;\n" ++
  s!"        valid <= 1'b1;\n" ++
  s!"      end\n" ++
  s!"      // Only dequeue\n" ++
  s!"      else if (deq_valid && deq_ready) begin\n" ++
  s!"        valid <= 1'b0;\n" ++
  s!"      end\n" ++
  s!"    end\n" ++
  s!"  end\n" ++
  s!"\n" ++
  s!"endmodule\n"

-- Generate Chisel for a Queue
def toChisel (q : QueueCircuit) : String :=
  let className := q.name
  let width := q.width

  s!"package generated\n" ++
  s!"\n" ++
  s!"import chisel3._\n" ++
  s!"import chisel3.util._\n" ++
  s!"\n" ++
  s!"class {className} extends Module \u007b\n" ++
  s!"  val enq_data = IO(Input(UInt({width}.W)))\n" ++
  s!"  val enq_valid = IO(Input(Bool()))\n" ++
  s!"  val enq_ready = IO(Output(Bool()))\n" ++
  s!"  val deq_data = IO(Output(UInt({width}.W)))\n" ++
  s!"  val deq_valid = IO(Output(Bool()))\n" ++
  s!"  val deq_ready = IO(Input(Bool()))\n" ++
  s!"\n" ++
  s!"  // State: valid bit and data storage\n" ++
  s!"  val valid = RegInit(false.B)\n" ++
  s!"  val data = RegInit(0.U({width}.W))\n" ++
  s!"\n" ++
  s!"  // Combinational outputs\n" ++
  s!"  enq_ready := !valid\n" ++
  s!"  deq_valid := valid\n" ++
  s!"  deq_data := data\n" ++
  s!"\n" ++
  s!"  // Sequential logic\n" ++
  "  when(reset.asBool) {\n" ++
  "    valid := false.B\n" ++
  "    data := 0.U\n" ++
  "  }.otherwise {\n" ++
  "    // Simultaneous enq and deq: flow through\n" ++
  "    when(enq_valid && enq_ready && deq_valid && deq_ready) {\n" ++
  "      data := enq_data\n" ++
  "      valid := true.B\n" ++
  "    }\n" ++
  "    // Only enqueue\n" ++
  "    .elsewhen(enq_valid && enq_ready) {\n" ++
  "      data := enq_data\n" ++
  "      valid := true.B\n" ++
  "    }\n" ++
  "    // Only dequeue\n" ++
  "    .elsewhen(deq_valid && deq_ready) {\n" ++
  "      valid := false.B\n" ++
  "    }\n" ++
  "  }\n" ++
  "}\n"

end Shoumei.Codegen.Queue
