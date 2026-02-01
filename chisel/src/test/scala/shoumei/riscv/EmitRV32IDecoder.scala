package shoumei.riscv

import circt.stage.ChiselStage

object EmitRV32IDecoder extends App {

  // Emit SystemVerilog for the RV32I decoder
  // Note: sbt runs from chisel/ directory, so ../ goes to project root
  ChiselStage.emitSystemVerilogFile(
    new RV32IDecoder,
    args = Array("--target-dir", "../output/sv-from-chisel"),
    firtoolOpts = Array("-disable-all-randomization", "-strip-debug-info")
  )

  println("✓ Generated SystemVerilog from Chisel: ../output/sv-from-chisel/RV32IDecoder.sv")
}
