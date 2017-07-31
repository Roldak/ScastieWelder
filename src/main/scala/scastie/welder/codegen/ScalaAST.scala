package scastie.welder.codegen

sealed abstract class ScalaAST
object ScalaAST {
  case class Raw(text: String) extends ScalaAST
  case class StringLiteral(lit: String) extends ScalaAST
  case class IntLiteral(lit: Int) extends ScalaAST

  case class Select(obj: ScalaAST, member: String) extends ScalaAST
  case class TypeApply(obj: ScalaAST, tps: Seq[ScalaAST]) extends ScalaAST
  case class Apply(obj: ScalaAST, args: Seq[ScalaAST]) extends ScalaAST
  case class Block(stmts: Seq[ScalaAST]) extends ScalaAST
  case class Ascript(obj: ScalaAST, tpe: ScalaAST) extends ScalaAST
  
  sealed abstract class Pattern
  case class ValDecl(id: String, tpe: Option[ScalaAST]) extends Pattern
  case class Unapply(extractor: ScalaAST, subpatterns: Seq[Pattern]) extends Pattern
  
  case class Case(pattern: Pattern, guard: Option[ScalaAST], body: ScalaAST)
  
  case class ValDef(decl: Pattern, rhs: ScalaAST) extends ScalaAST
  case class Match(selector: ScalaAST, cases: Seq[Case]) extends ScalaAST
  case class Lambda(params: Seq[Pattern], body: ScalaAST) extends ScalaAST
  case class Tuple(elems: Seq[ScalaAST]) extends ScalaAST

  object Implicits {
    implicit class Api(val ast: ScalaAST) extends AnyVal {
      def apply(arg0: ScalaAST): ScalaAST = Apply(ast, Seq(arg0))
      def apply(arg0: ScalaAST, arg1: ScalaAST): ScalaAST = Apply(ast, Seq(arg0, arg1))
      def apply(arg0: ScalaAST, arg1: ScalaAST, arg2: ScalaAST): ScalaAST = Apply(ast, Seq(arg0, arg1, arg2))
      def apply(arg0: ScalaAST, arg1: ScalaAST, arg2: ScalaAST, arg3: ScalaAST): ScalaAST = Apply(ast, Seq(arg0, arg1, arg2, arg3))
      def apply(args: Seq[ScalaAST]): ScalaAST = Apply(ast, args)

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