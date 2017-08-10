lazy val baseSettings = Defaults.defaultSettings ++ Seq(
  organization := "ch.epfl.lara",
  version := "0.0.1",
  scalaVersion := "2.11.8",
  scalacOptions ++= Seq(
    "-Yrangepos"
  )
)
lazy val scastieWelder = Project(
  "ScastieWelder", 
  file("."),
  settings = baseSettings ++ Seq(
    libraryDependencies += "ch.epfl.lara" %% "welder" % "0.1",
    libraryDependencies += "org.scalameta" %% "scalameta" % "1.8.0",
    libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value
  )
)