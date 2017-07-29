package scastie.welder.codegen

sealed abstract class ScalaAST
object ScalaAST {
  case class Raw(text: String) extends ScalaAST
  case class StringLiteral(lit: String) extends ScalaAST
  case class IntLiteral(lit: Int) extends ScalaAST

  case class Select(obj: ScalaAST, member: String) extends ScalaAST
  case class Invocation(obj: ScalaAST, args: Seq[ScalaAST]) extends ScalaAST
  case class Block(stmts: Seq[ScalaAST]) extends ScalaAST

  case class ValDecl(id: String, tpe: Option[ScalaAST])
  case class ValDef(decl: ValDecl, rhs: ScalaAST) extends ScalaAST
  case class Lambda(params: Seq[ValDecl], body: ScalaAST) extends ScalaAST

  object Implicits {
    implicit class Api(val ast: ScalaAST) extends AnyVal {
      def apply(arg0: ScalaAST): ScalaAST = Invocation(ast, Seq(arg0))
      def apply(arg0: ScalaAST, arg1: ScalaAST): ScalaAST = Invocation(ast, Seq(arg0, arg1))
      def apply(arg0: ScalaAST, arg1: ScalaAST, arg2: ScalaAST): ScalaAST = Invocation(ast, Seq(arg0, arg1, arg2))
      def apply(arg0: ScalaAST, arg1: ScalaAST, arg2: ScalaAST, arg3: ScalaAST): ScalaAST = Invocation(ast, Seq(arg0, arg1, arg2, arg3))
      def apply(args: Seq[ScalaAST]): ScalaAST = Invocation(ast, args)

      def `.`(member: String): ScalaAST = Select(ast, member)
    }

    implicit class StringHelpers(val str: String) extends AnyVal {
      def ::(tpe: ScalaAST): ValDecl = ValDecl(str, Some(tpe))
      def `.`(member: String): ScalaAST = Select(StringLiteral(str), member)
    }

    implicit def string2StringLiteral(str: String): StringLiteral = StringLiteral(str)
    implicit def string2ValDecl(str: String): ValDecl = ValDecl(str, None)
  }
}