// Shoumei RTL - Chisel Build Configuration
// Scala 2.13 with Chisel 7.x

// Shared version constants
val chiselVersion = "7.7.0"
val scalaVer = "2.13.18"  // Required for Chisel 7.7.0

ThisBuild / scalaVersion := scalaVer
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "com.shoumei"

lazy val root = (project in file("."))
  .settings(
    name := "shoumei-rtl-chisel",


    libraryDependencies ++= Seq(
      "org.chipsalliance" %% "chisel" % chiselVersion
    ),

    scalacOptions ++= Seq(
      "-language:reflectiveCalls",
      "-deprecation",
      "-feature",
      "-Xcheckinit",
      "-Xfatal-warnings"
    ),

    addCompilerPlugin("org.chipsalliance" % "chisel-plugin" % chiselVersion cross CrossVersion.full)
  )

// Note: Using Chisel 7.7.0 (latest stable as of 2026-01-31)
// Chisel 7.x+ automatically manages firtool binary
// TODO: Add chiseltest dependency once available for 7.x
