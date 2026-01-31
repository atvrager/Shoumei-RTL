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

object Main extends App {
  println("証明 Shoumei RTL - Chisel to SystemVerilog Compiler")
  println("=" * 50)
  println()

  // Stub module for testing (used only if no generated modules found)
  class StubModule extends Module {

    val io = IO(new Bundle {
      val in  = Input(Bool())
      val out = Output(Bool())
    })
    io.out := io.in
  }

  // Try to compile generated modules
  // This uses dynamic class loading to avoid compile-time dependency on generated package
  def compileModule(moduleName: String): Boolean =
    try {
      println(s"Compiling $moduleName...")

      // Use ChiselStage with a generator function
      // The generator is called lazily, allowing us to load the class dynamically
      val generatorFn = () => {
        val moduleClass = Class.forName(s"generated.$moduleName")
        // Get the primary constructor
        val constructor = moduleClass.getDeclaredConstructors()(0)
        constructor.setAccessible(true)
        constructor.newInstance().asInstanceOf[RawModule]
      }

      val projectRoot = new File(System.getProperty("user.dir")).getParentFile
      val outputDir   = new File(projectRoot, "output/sv-from-chisel")
      outputDir.mkdirs()

      // Generate SystemVerilog using ChiselStage
      // Note: ChiselStage.emitSystemVerilog handles Module construction properly
      ChiselStage.emitSystemVerilogFile(
        generatorFn(),
        args = Array("--target-dir", outputDir.getAbsolutePath)
      )

      println(s"✓ $moduleName compilation successful")
      println(s"Output: ${new File(outputDir, s"$moduleName.sv").getAbsolutePath}")
      true
    } catch {
      case e: ClassNotFoundException =>
        println(s"⚠ $moduleName class not found")
        false
      case e: Exception =>
        println(s"✗ $moduleName compilation failed: ${e.getMessage}")
        e.printStackTrace()
        false
    }

  // Discover generated modules in src/main/scala/generated/
  def discoverGeneratedModules(): List[String] = {
    val genDir = new File("src/main/scala/generated")
    if (!genDir.exists() || !genDir.isDirectory) {
      return List()
    }

    val files = genDir.listFiles()
    if (files == null) return List()

    files
      .filter(f => f.isFile && f.getName.endsWith(".scala") && f.getName != ".gitkeep")
      .map(_.getName.replace(".scala", ""))
      .toList
  }

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
        println(s"✗ Stub compilation failed: ${e.getMessage}")
        e.printStackTrace()
        sys.exit(1)
    }
  } else {
    println(s"Found ${modules.length} generated module(s): ${modules.mkString(", ")}")
    println()

    // Try to compile each discovered module
    var successCount = 0
    for (moduleName <- modules) {
      if (compileModule(moduleName)) {
        successCount += 1
      }
      println()
    }

    if (successCount == 0) {
      println("✗ No modules compiled successfully")
      sys.exit(1)
    } else {
      println(s"✓ $successCount/${modules.length} module(s) compiled successfully")
    }
  }

  println()
  println("✓ Chisel compilation complete")
}
