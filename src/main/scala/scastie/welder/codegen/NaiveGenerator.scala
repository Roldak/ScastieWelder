package scastie.welder.codegen

import scala.meta._

class NaiveGenerator extends ScalaCodeGenerator {
  import ScalaAST._

  private def genPattern(pattern: Pattern): String = pattern match {
    case ValDecl(id, Some(tpe))  => s"$id: ${gen(tpe)}"
    case ValDecl(id, None)       => id
    case Unapply(extr, patterns) => s"$extr(${patterns map genPattern mkString ", "})"
  }

  private def gen(ast: ScalaAST): String = ast match {
    case Raw(text)            => text
    case StringLiteral(lit)   => s""""$lit""""
    case IntLiteral(lit)      => lit.toString

    case Select(obj, member)  => s"(${gen(obj)}).$member"
    case TypeApply(obj, tps)  => s"(${gen(obj)})[${tps map gen mkString ", "}]"
    case Apply(obj, args)     => s"(${gen(obj)})(${args map gen mkString ", "})"
    case Block(stmts)         => s"{${stmts map gen mkString "; "}}"
    case Ascript(obj, tpe)    => s"${gen(obj)}: ${gen(tpe)}"

    case ValDef(pattern, rhs) => s"val ${genPattern(pattern)} = ${gen(rhs)}"

    case Lambda(params, body) => s"{ case (${params map genPattern mkString ", "}) => ${gen(body)} }"
    case Tuple(elems)         => s"(${elems map gen mkString ", "})"
  }

  override def generateScalaCode(ast: ScalaAST): String = {
    val res = gen(ast)
    
    val parsed = res.parse[Stat]
    
    parsed match {
      case Parsed.Success(tree) =>
        println(s"$tree, ${tree.structure}, ${tree.syntax}")
      case _ =>
    }
    
    res
  }
}