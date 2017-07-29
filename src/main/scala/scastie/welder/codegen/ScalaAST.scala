package scastie.welder.codegen

sealed abstract class ScalaAST
object ScalaAST {
  case class Raw(text: String) extends ScalaAST
  case class StringLiteral(lit: String) extends ScalaAST
  case class IntLiteral(lit: Int) extends ScalaAST

  case class Select(obj: ScalaAST, member: String) extends ScalaAST
  case class Invocation(obj: ScalaAST, args: Seq[ScalaAST]) extends ScalaAST
  case class Block(stmts: Seq[ScalaAST]) extends ScalaAST
  case class Ascript(obj: ScalaAST, tpe: ScalaAST) extends ScalaAST
  
  sealed abstract class Pattern
  case class ValDecl(id: String, tpe: Option[ScalaAST]) extends Pattern
  case class Unapply(extractor: String, subpatterns: Seq[Pattern]) extends Pattern
  
  case class ValDef(decl: Pattern, rhs: ScalaAST) extends ScalaAST
  case class Lambda(params: Seq[Pattern], body: ScalaAST) extends ScalaAST

  object Implicits {
    implicit class Api(val ast: ScalaAST) extends AnyVal {
      def apply(arg0: ScalaAST): ScalaAST = Invocation(ast, Seq(arg0))
      def apply(arg0: ScalaAST, arg1: ScalaAST): ScalaAST = Invocation(ast, Seq(arg0, arg1))
      def apply(arg0: ScalaAST, arg1: ScalaAST, arg2: ScalaAST): ScalaAST = Invocation(ast, Seq(arg0, arg1, arg2))
      def apply(arg0: ScalaAST, arg1: ScalaAST, arg2: ScalaAST, arg3: ScalaAST): ScalaAST = Invocation(ast, Seq(arg0, arg1, arg2, arg3))
      def apply(args: Seq[ScalaAST]): ScalaAST = Invocation(ast, args)

      def `.`(member: String): ScalaAST = Select(ast, member)
      def `:`(tpe: ScalaAST): ScalaAST = Ascript(ast, tpe)
    }

    implicit class StringHelpers(val str: String) extends AnyVal {
      def `.`(member: String): ScalaAST = Select(StringLiteral(str), member)
    }

    implicit def string2StringLiteral(str: String): StringLiteral = StringLiteral(str)
    implicit def string2ValDecl(str: String): ValDecl = ValDecl(str, None)
    implicit def stringSeq2StringLiteralSeq(strs: Seq[String]): Seq[StringLiteral] = strs map string2StringLiteral
    implicit def stringSeq2ValDeclSeq(strs: Seq[String]): Seq[ValDecl] = strs map string2ValDecl
  }
}