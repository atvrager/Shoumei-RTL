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
import scala.io.Source

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

  // Read the package declaration from a Scala source file
  def getPackageName(file: File): String = {
    val source = Source.fromFile(file)
    try
      source
        .getLines()
        .map(_.trim)
        .find(_.startsWith("package "))
        .map(_.stripPrefix("package ").trim)
        .getOrElse("generated")
    finally
      source.close()
  }

  // Get module info (name, fully-qualified class name) from a generated source file
  def moduleInfo(file: File): (String, String) = {
    val moduleName  = file.getName.replace(".scala", "")
    val packageName = getPackageName(file)
    (moduleName, s"$packageName.$moduleName")
  }

  // Try to compile a generated module using reflection
  // This avoids compile-time dependency on generated packages
  def compileModule(moduleName: String, fqClassName: String): Boolean =
    try {
      println(s"Compiling $moduleName ($fqClassName)...")

      val generatorFn = () => {
        val moduleClass = Class.forName(fqClassName)
        val constructor = moduleClass.getDeclaredConstructors()(0)
        constructor.setAccessible(true)
        constructor.newInstance().asInstanceOf[RawModule]
      }

      val projectRoot = new File(System.getProperty("user.dir")).getParentFile
      val outputDir   = new File(projectRoot, "output/sv-from-chisel")
      outputDir.mkdirs()

      ChiselStage.emitSystemVerilogFile(
        generatorFn(),
        args = Array("--target-dir", outputDir.getAbsolutePath),
        firtoolOpts = Array("-disable-all-randomization", "-strip-debug-info")
      )

      println(s"✓ $moduleName compilation successful")
      println(s"Output: ${new File(outputDir, s"$moduleName.sv").getAbsolutePath}")
      true
    } catch {
      case e: ClassNotFoundException =>
        println(s"⚠ $moduleName class not found ($fqClassName)")
        false
      case e: Exception =>
        println(s"✗ $moduleName compilation failed: ${e.getMessage}")
        e.printStackTrace()
        false
    }

  // Discover generated modules in src/main/scala/generated/
  // Returns (moduleName, fullyQualifiedClassName) pairs
  def discoverGeneratedModules(): List[(String, String)] = {
    val genDir = new File("src/main/scala/generated")
    if (!genDir.exists() || !genDir.isDirectory) {
      return List()
    }

    val files = genDir.listFiles()
    if (files == null) return List()

    files
      .filter(f => f.isFile && f.getName.endsWith(".scala") && f.getName != ".gitkeep")
      .map(moduleInfo)
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
    println(s"Found ${modules.length} generated module(s): ${modules.map(_._1).mkString(", ")}")
    println()

    var successCount = 0
    for ((moduleName, fqClassName) <- modules) {
      if (compileModule(moduleName, fqClassName)) {
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
