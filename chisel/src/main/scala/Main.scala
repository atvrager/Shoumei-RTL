// Main.scala - Entry point for Chisel to SystemVerilog compilation
//
// This program:
// 1. Loads generated Chisel modules from src/main/scala/generated/
// 2. Compiles them to SystemVerilog using ChiselStage and firtool
// 3. Outputs SystemVerilog to ../../output/sv-from-chisel/
//
// Note: Chisel 7.x auto-manages firtool binary

import chisel3._
import circt.stage.ChiselStage

object Main extends App {
  println("Proven RTL - Chisel to SystemVerilog Compiler")
  println("=" * 50)

  // TODO: Load and compile generated Chisel modules
  // For now, compile a stub empty module to verify the toolchain works

  // Stub module for testing
  class StubModule extends Module {
    val io = IO(new Bundle {
      val in = Input(Bool())
      val out = Output(Bool())
    })
    io.out := io.in
  }

  println("Compiling stub module...")

  try {
    // Compile to SystemVerilog using ChiselStage
    // This uses firtool (CIRCT) backend automatically in Chisel 6.x
    ChiselStage.emitSystemVerilogFile(
      new StubModule,
      args = Array(
        "--target-dir", "../../output/sv-from-chisel"
      )
    )

    println("✓ Compilation successful")
    println("Output written to: output/sv-from-chisel/")
  } catch {
    case e: Exception =>
      println(s"✗ Compilation failed: ${e.getMessage}")
      e.printStackTrace()
      sys.exit(1)
  }

  // TODO: In the future, dynamically discover and compile all modules
  // in src/main/scala/generated/ directory
  //
  // Example:
  // val generatedModules = discoverGeneratedModules()
  // for (module <- generatedModules) {
  //   compileModule(module)
  // }
}
