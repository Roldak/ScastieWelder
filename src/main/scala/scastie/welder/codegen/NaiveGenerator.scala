package scastie.welder.codegen

import scala.meta._

class NaiveGenerator extends ScalaCodeGenerator {
  import ScalaAST._

  private def gen(ast: ScalaAST): String = ast match {
    case Raw(text) => text
    case StringLiteral(lit) => s""""$lit""""
    case IntLiteral(lit) => lit.toString
    
    case Select(obj, member) => s"""${gen(obj)}.$member"""
    case Invocation(obj, args) => s"${gen(obj)}(${args map gen mkString ", "})"
    case Block(stmts) => s"{stmts map gen mkString "; "}"
    
    case ValDef(ValDecl(id, Some(tpe)), rhs) => s"val id: ${gen(tpe)} = ${gen(rhs)}"
    case ValDef(ValDecl(id, None), rhs) => s"val id = ${gen(rhs)}"
    case Lambda(params, body) => 
      val paramsstr = params map {
        case ValDecl(id, Some(tpe)) => s"$id: ${gen(tpe)}"
        case ValDecl(id, None) => id
      }
      s"(${paramsstr mkString ", "}) => ${gen(body)}"
  }

  override def generateScalaCode(ast: ScalaAST): String = {
    val res = gen(ast)
    val parsed = res.parse[Stat]
    println(parsed)
    parsed match {
      case Parsed.Success(tree) =>
        println(s"$tree, ${tree.structure}, $tree.syntax")
      case _ =>
    }
    res
  }
}