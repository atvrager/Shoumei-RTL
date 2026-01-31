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
import java.io.File
import scala.util.{Try, Success, Failure}

object Main extends App {
  println("証明 Shoumei RTL - Chisel to SystemVerilog Compiler")
  println("=" * 50)
  println()

  // Discover generated modules in src/main/scala/generated/
  def discoverGeneratedModules(): List[String] = {
    val genDir = new File("src/main/scala/generated")
    if (!genDir.exists() || !genDir.isDirectory) {
      return List()
    }

    genDir.listFiles()
      .filter(f => f.isFile && f.getName.endsWith(".scala"))
      .map(_.getName.replace(".scala", ""))
      .toList
  }

  // Stub module for testing (used only if no generated modules found)
  class StubModule extends Module {
    val io = IO(new Bundle {
      val in = Input(Bool())
      val out = Output(Bool())
    })
    io.out := io.in
  }

  // Discover what modules we have
  val modules = discoverGeneratedModules()

  if (modules.isEmpty) {
    println("⚠ No generated modules found in src/main/scala/generated/")
    println("Compiling stub module for toolchain verification...")
    println()

    try {
      ChiselStage.emitSystemVerilogFile(
        new StubModule,
        args = Array("--target-dir", "../../output/sv-from-chisel")
      )
      println("✓ Stub compilation successful")
      println("Output: output/sv-from-chisel/StubModule.sv")
    } catch {
      case e: Exception =>
        println(s"✗ Compilation failed: ${e.getMessage}")
        e.printStackTrace()
        sys.exit(1)
    }
  } else {
    println(s"Found ${modules.length} generated module(s): ${modules.mkString(", ")}")
    println()

    // For now, specifically compile FullAdder if it exists
    if (modules.contains("FullAdder")) {
      println("Compiling FullAdder...")

      try {
        // Dynamically load the generated.FullAdder class using reflection
        val fullAdderClass = Class.forName("generated.FullAdder")
        val constructor = fullAdderClass.getConstructors()(0)
        val fullAdderInstance = constructor.newInstance().asInstanceOf[Module]

        // Generate SystemVerilog string
        val sv = ChiselStage.emitSystemVerilog(fullAdderInstance)

        // Write to file - use absolute path to avoid path resolution issues
        val projectRoot = new File(System.getProperty("user.dir")).getParentFile
        val outputDir = new File(projectRoot, "output/sv-from-chisel")
        outputDir.mkdirs()
        val outputFile = new File(outputDir, "FullAdder.sv")

        val writer = new java.io.PrintWriter(outputFile)
        try {
          writer.write(sv)
        } finally {
          writer.close()
        }

        println("✓ FullAdder compilation successful")
        println(s"Output: ${outputFile.getAbsolutePath}")
      } catch {
        case e: ClassNotFoundException =>
          println(s"✗ FullAdder class not found (this shouldn't happen)")
          println("   Make sure LEAN codegen has run successfully")
          sys.exit(1)
        case e: Exception =>
          println(s"✗ Compilation failed: ${e.getMessage}")
          e.printStackTrace()
          sys.exit(1)
      }
    } else {
      println("⚠ FullAdder.scala not found in generated modules")
      println("   Run 'make codegen' to generate modules from LEAN")
      sys.exit(1)
    }
  }

  println()
  println("✓ Chisel compilation complete")
}
