package scastie.welder.codegen

trait ScalaCodeGenerator {
  def generateScalaCode(ast: ScalaAST): String
}