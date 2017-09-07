package scastie.welder.codegen

class NaiveGenerator extends ScalaCodeGenerator {
  import ScalaAST._
  import scastie.welder.Constants._
  import scastie.welder.Constants.Implicits._

  private val letter: Set[Char] = ('a' to 'z').toSet ++ ('A' to 'Z').toSet

  private def precedenceOf(selector: CleanString): Int = {
    require(selector.str.size > 0)
    selector.str.head match {
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

  private def isLeftAssociative(selector: CleanString): Boolean = {
    require(selector.str.size > 0)
    selector.str.last != ':'
  }

  private def isOperator(selector: CleanString): Boolean = !selector.str.exists(letter)

  private object Operator {
    def unapply(s: String): Option[String] = if (isOperator(s)) Some(s) else None
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
  }

  private def isSingleLine(x: String): Boolean = !x.exists(_ == '\n')

  private case class PrettyPrinter(indent: Int, parents: List[ScalaAST]) {
    private lazy val newline = "\n" + "  " * indent
    private lazy val newline2 = newline + "  "

    private def indented = copy(indent = indent + 1)
    private def indented(count: Int) = copy(indent = indent + count)

    private def from(parent: ScalaAST) = copy(parents = parent :: parents)
    private def fresh = copy(parents = Nil)

    def parent = parents.head
    def hasParent = !parents.isEmpty

    def genOpTree(tree: OpTree)(precedence: Int): String = tree match {
      case OpNode(lhs, op, rhs) =>
        val opPrecedence = precedenceOf(op)
        val left = genOpTree(lhs)(opPrecedence)
        val right = genOpTree(rhs)(opPrecedence)

        val res = if (isLeftAssociative(op))
          s"$left $op $right"
        else
          s"$right $op $left"

        if (opPrecedence < precedence) s"(${res})"
        else res

      case OpLeaf(ast) => gen(ast)
    }

    def genPattern(pattern: Pattern): String = pattern match {
      case ValDecl(id, Some(tpe))  => s"$id: ${gen(tpe)}"
      case ValDecl(id, None)       => id
      case Unapply(extr, patterns) => s"${gen(extr)}(${patterns map genPattern mkString ", "})"
      case BackTicks(id)           => s"`$id`"
    }

    def genCase(c: Case): String = {
      val pat = genPattern(c.pattern)
      val guard = c.guard.map(g => s"if ${gen(g)} ").getOrElse("")
      val body = indented.gen(c.body)

      s"case $pat $guard => $newline2$body"
    }

    def genFuncParams(params: Seq[ValDecl]): String = params match {
      case Seq(param) => genPattern(param)
      case _          => s"(${params map genPattern mkString ", "})"
    }

    def gen(ast: ScalaAST): String = {
      def rec = from(ast)

      val isInBlock = hasParent && (parent match {
        case _: Block | _: Function | _: PartialFunction => true
        case _ => false
      })

      val res = ast match {
        case Raw(text)                           => text
        case StringLiteral(lit)                  => s""""$lit""""
        case IntLiteral(lit)                     => lit.toString

        case Select(obj, member)                 => s"${rec.gen(obj)}.$member"
        case TypeApply(obj, tps)                 => s"${rec.gen(obj)}[${tps map fresh.gen mkString ", "}]"
        case OpTree(tree)                        => genOpTree(tree)(0)
        case Apply(obj, Seq(f: Function))        => s"${rec.gen(obj)} ${fresh.gen(f)}"
        case Apply(obj, Seq(f: PartialFunction)) => s"${rec.gen(obj)} ${fresh.gen(f)}"
        case Apply(obj, args)                    => s"${rec.gen(obj)}(${args map fresh.gen mkString ", "})"
        case Block(stmts) if isInBlock           => stmts map rec.fresh.gen mkString newline
        case Block(stmts)                        => s"{${newline2}${stmts map rec.fresh.gen mkString newline2}${newline}}"

        case Ascript(obj, tpe)                   => s"${rec.gen(obj)}: ${rec.gen(tpe)}"

        case ValDef(pattern, rhs)                => s"val ${fresh.genPattern(pattern)} = ${rec.gen(rhs)}"
        case Match(sel, cases)                   => s"${rec.gen(sel)} match {${newline2}${cases map indented.fresh.genCase mkString s"$newline2$newline2"}${newline}}"
        case Function(params, body)              => s"{ ${fresh.genFuncParams(params)} => ${newline2}${rec.indented.gen(body)}${newline}}"
        case PartialFunction(cases)              => s"{${newline2}${cases map indented.fresh.genCase mkString s"$newline2$newline2"}${newline}}"
        case Tuple(elems)                        => s"(${elems map fresh.gen mkString ", "})"
      }

      if (hasParent) {
        val mustPar = ast match {
          case _: Raw | _: StringLiteral | _: IntLiteral => false
          case _: Select | _: TypeApply | _: Apply       => false
          case _: Tuple | _: Block                       => false

          case _                                         => true
        }

        if (mustPar) s"(${res})"
        else res
      } else res
    }

  }

  override def generateScalaCode(ast: ScalaAST): String = PrettyPrinter(0, Nil).gen(ast)
}