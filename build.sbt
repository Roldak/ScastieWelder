lazy val baseSettings = Defaults.defaultSettings ++ Seq(
  organization := "ch.epfl.lara",
  version := "0.0.1",
  scalaVersion := "2.12.2",
  scalacOptions ++= Seq(
    "-Yrangepos"
  )
)
lazy val scastieWelder = Project(
  "ScastieWelder", 
  file("."),
  settings = baseSettings ++ Seq(
    libraryDependencies += "ch.lara.epfl" % "welder_2.11" % "0.1",
    libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value
  )
)