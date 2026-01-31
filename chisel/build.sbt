// Proven RTL - Chisel Build Configuration
// Scala 3 with Chisel 7.x

ThisBuild / scalaVersion := "3.3.4"
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "com.provenrtl"

lazy val root = (project in file("."))
  .settings(
    name := "proven-rtl-chisel",
    libraryDependencies ++= Seq(
      "org.chipsalliance" %% "chisel" % "7.0.0",
      "org.chipsalliance" %% "chisel-plugin" % "7.0.0" cross CrossVersion.full,
      "org.chipsalliance" %% "chiseltest" % "7.0.0" % "test"
    ),
    scalacOptions ++= Seq(
      "-language:reflectiveCalls",
      "-deprecation",
      "-feature",
      "-Xcheckinit",
      "-Xfatal-warnings"
    ),
    addCompilerPlugin("org.chipsalliance" % "chisel-plugin" % "6.6.0" cross CrossVersion.full)
  )

// Note: Chisel 7.x automatically manages firtool binary
// No manual CIRCT/firtool installation needed
