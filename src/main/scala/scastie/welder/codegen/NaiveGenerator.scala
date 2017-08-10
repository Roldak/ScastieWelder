package scastie.welder.codegen

import scala.meta._

class NaiveGenerator extends ScalaCodeGenerator {
  import ScalaAST._

  private case class GenContext(parents: List[ScalaAST]) {
    def withParent(parent: ScalaAST) = copy(parents = parent :: parents)
    def parent = parents.head
    def hasParent = !parents.isEmpty
  }

  private val emptyContext = GenContext(Nil)

  private val letter: Set[Char] = ('a' to 'z').toSet ++ ('A' to 'Z').toSet

  private def precedenceOf(selector: String): Int = {
    require(selector.size > 0)
    selector.head match {
      case chr if letter(chr) => 0
      case '|'                => 1
      case '^'                => 2
      case '&'                => 3
      case '=' | '!'          => 4
      case '<' | '>'          => 5
      case ':'                => 6
      case '+' | '-'          => 7
      case '*' | '/' | '%'    => 8
      case _                  => 9
    }
  }

  private def isLeftAssociative(selector: String): Boolean = {
    require(selector.size > 0)
    selector.last != ':'
  }
  
  private def isOperator(selector: String): Boolean = !selector.exists(letter)
  
  private object Operator {
    def unapply(s: String): Option[String] = if (isOperator(s)) Some(s) else None
  }

  private def genPattern(pattern: Pattern): String = pattern match {
    case ValDecl(id, Some(tpe))  => s"$id: ${gen(tpe)(emptyContext)}"
    case ValDecl(id, None)       => id
    case Unapply(extr, patterns) => s"${gen(extr)(emptyContext)}(${patterns map genPattern mkString ", "})"
  }

  private def genCase(c: Case)(ctx: GenContext): String = c match {
    case Case(pattern, Some(guard), body) => s"case ${genPattern(pattern)} if ${gen(guard)(emptyContext)} => ${gen(body)(emptyContext)}"
    case Case(pattern, None, body)        => s"case ${genPattern(pattern)} => ${gen(body)(emptyContext)}"
  }

  private sealed abstract class OpTree
  private case class OpNode(lhs: OpTree, op: String, rhs: OpTree) extends OpTree
  private case class OpLeaf(ast: ScalaAST) extends OpTree

  private object OpTree {
    def unapply(ast: ScalaAST): Option[OpTree] = {
      object Inner {
        def unapply(ast: ScalaAST): Option[OpTree] = ast match {
          case Apply(Select(Inner(lhs), Operator(op)), Seq(Inner(rhs))) => Some(OpNode(lhs, op, rhs))
          case _ => Some(OpLeaf(ast))
        }
      }

      ast match {
        case Apply(Select(Inner(lhs), Operator(op)), Seq(Inner(rhs))) => Some(OpNode(lhs, op, rhs))
        case _ => None
      }
    }

    def render(tree: OpTree)(ctx: GenContext, precedence: Int = 0): String = tree match {
      case OpNode(lhs, op, rhs) =>
        val opPrecedence = precedenceOf(op)
        val left = render(lhs)(ctx, opPrecedence)
        val right = render(rhs)(ctx, opPrecedence)

        val res = if (isLeftAssociative(op))
          s"$left $op $right"
        else
          s"$right $op $left"

        if (opPrecedence < precedence) s"(${res})"
        else res

      case OpLeaf(ast) => gen(ast)(ctx)
    }
  }

  private def gen(ast: ScalaAST)(ctx: GenContext): String = {
    val nextCtx = ctx withParent ast
    def recGen(ast: ScalaAST) = gen(ast)(nextCtx)
    def newGen(ast: ScalaAST) = gen(ast)(emptyContext)

    val res = ast match {
      case Raw(text)              => text
      case StringLiteral(lit)     => s""""$lit""""
      case IntLiteral(lit)        => lit.toString

      case Select(obj, member)    => s"${recGen(obj)}.$member"
      case TypeApply(obj, tps)    => s"${recGen(obj)}[${tps map newGen mkString ", "}]"
      case OpTree(tree)           => OpTree.render(tree)(nextCtx)
      case Apply(obj, args)       => s"${recGen(obj)}(${args map newGen mkString ", "})"
      case Block(stmts)           => s"{${stmts map newGen mkString "; "}}"
      case Ascript(obj, tpe)      => s"${recGen(obj)}: ${recGen(tpe)}"

      case ValDef(pattern, rhs)   => s"val ${genPattern(pattern)} = ${recGen(rhs)}"
      case Match(sel, cases)      => s"${recGen(sel)} match { ${cases map genCase mkString " "} }"
      case Function(params, body) => s"(${params map genPattern mkString ", "}) => ${recGen(body)}"
      case PartialFunction(cases) => s"{ ${cases map genCase mkString " "} }"
      case Tuple(elems)           => s"(${elems map newGen mkString ", "})"
    }

    if (ctx.hasParent) {
      val parent = ctx.parent

      val mustPar = ast match {
        case _: Raw | _: StringLiteral | _: IntLiteral => false
        case _: Select | _: TypeApply | _: Apply       => false
        case _: Tuple                                  => false
        case _                                         => true
      }

      if (mustPar) s"(${res})"
      else res
    } else res
  }

  override def generateScalaCode(ast: ScalaAST): String = {
    val res = gen(ast)(emptyContext)

    val parsed = res.parse[Stat]

    parsed match {
      case Parsed.Success(tree) => println(tree.syntax)
      case _                    =>
    }

    res
  }
}