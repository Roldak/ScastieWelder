package scastie.welder.macros

import scala.reflect.macros.blackbox.Context
import scala.reflect.macros.TypecheckException

trait ContextAnalysis { self: Macros =>
  val c: Context

  import c.universe._
  import scastie.welder.Constants

  protected[macros] class ValOrDefDefCollector(val before: Tree) extends Traverser {
    private var valdefs: List[ValOrDefDef] = _
    private var stillCollecting = true

    def findAll(t: Tree): List[ValOrDefDef] = {
      valdefs = Nil
      super.traverse(t)
      valdefs
    }

    override def traverse(t: Tree): Unit = t match {
      case tree if tree == before             => stillCollecting = false
      case vd: ValOrDefDef if stillCollecting => valdefs ::= vd
      case _                                  =>
    }
  }

  protected[macros] object ValOrDefDefCollector {
    def apply(tree: Tree, before: Tree = null): List[ValOrDefDef] = (new ValOrDefDefCollector(before)).findAll(tree)
  }

  protected[macros] def collectBinds(pattern: Tree): Set[Bind] = pattern.collect {
    case b: Bind => b
  } toSet

  protected[macros] lazy val pathToMacro = IOTraverser[Option[List[Tree]]](None) {
    case (tree, _) if tree.pos == c.macroApplication.pos => Some(tree :: Nil)
    case (other, rec)                                    => rec.children(other)(_.find(_ != None).getOrElse(None)).map(other :: _)
  }(c.enclosingPackage).get

  protected[macros] lazy val reachableDefs: Set[DefTree] = {
    case class Input(path: List[Tree], inClosedScope: Boolean) {
      def next = copy(path = path.tail)
      def next(isInClosedScope: Boolean) = copy(path = path.tail, inClosedScope = isInClosedScope)

      def isPrefix(tree: Tree): Boolean = path != Nil && path.head == tree
    }
    type Output = Set[DefTree]

    implicit def mergeOutputs(outs: Seq[Output]): Output = outs.flatten.toSet

    val traverser = IOTraverser[Input, Output](Set.empty) {
      case (tree, input, rec) if input.isPrefix(tree) => {
        val output = tree match {
          case Template(_, self, body)         => rec.some(body, input.next(false)) ++ ValOrDefDefCollector(tree)
          case DefDef(_, _, _, params, _, rhs) => rec.one(rhs, input.next(true)) ++ params.flatten
          case Function(params, body)          => rec.one(body, input.next(true)) ++ params
          case CaseDef(pat, _, body)           => rec.one(body, input.next) ++ collectBinds(pat)
          case _                               => rec.children(tree, input.next)
        }

        if (input.inClosedScope) {
          output ++ ValOrDefDefCollector(tree, tree.children.find(input.next.isPrefix).getOrElse(null))
        } else {
          output
        }
      }
    }

    c.enclosingRun.units.map {
      unit => traverser(unit.body, Input(pathToMacro, false))
    }.flatten.toSet
  }

  protected[macros] sealed abstract class Rel {
    override def toString: String = this match {
      case Rel.LE => Constants.Rel.LE
      case Rel.LT => Constants.Rel.LT
      case Rel.EQ => Constants.Rel.EQ
      case Rel.GT => Constants.Rel.GT
      case Rel.GE => Constants.Rel.GE
    }
  }

  protected[macros] object Rel {
    def unapply(t: TermName): Option[Rel] = t.decodedName.toString match {
      case "<=|" => Some(LE)
      case "<<|" => Some(LT)
      case "==|" => Some(EQ)
      case ">>|" => Some(GT)
      case ">=|" => Some(GE)
      case _     => None
    }

    implicit val relLifter: Liftable[Rel] = Liftable[Rel] {
      case Rel.LE => q"${c.prefix}.relations.LE"
      case Rel.LT => q"${c.prefix}.relations.LT"
      case Rel.EQ => q"${c.prefix}.relations.EQ"
      case Rel.GT => q"${c.prefix}.relations.GT"
      case Rel.GE => q"${c.prefix}.relations.GE"
    }

    case object LE extends Rel
    case object LT extends Rel
    case object EQ extends Rel
    case object GT extends Rel
    case object GE extends Rel
  }

  protected[macros] trait OpChainSegment {
    def lhs: Tree
    def op: Rel
    def rhs: Tree
    def proof: Tree
  }

  protected[macros] object OpChainSegment {
    def unapply(x: OpChainSegment): Option[(Tree, Rel, Tree, Tree)] = Some((x.lhs, x.op, x.rhs, x.proof))
  }

  protected[macros] sealed abstract class OpChainTree {
    final def leftMost: OpChainLeaf = this match {
      case OpChainNode(prev, next) => prev.leftMost
      case leaf: OpChainLeaf       => leaf
    }

    final def rightMost: OpChainLeaf = this match {
      case OpChainNode(prev, next) => next.rightMost
      case leaf: OpChainLeaf       => leaf
    }
  }

  protected[macros] case class OpChainNode(prev: OpChainTree, next: OpChainTree) extends OpChainTree with OpChainSegment {
    override def lhs = prev.rightMost.expr
    override def op = prev.rightMost.op
    override def rhs = next.leftMost.expr
    override def proof = prev.rightMost.proof
  }

  protected[macros] case class OpChainLeaf(expr: Tree, op: Rel, proof: Tree) extends OpChainTree

  protected[macros] case class OpChain(root: OpChainTree, expr: Tree, pos: Position) extends OpChainSegment {
    override def lhs = root.rightMost.expr
    override def op = root.rightMost.op
    override def rhs = expr
    override def proof = root.rightMost.proof
  }

  private val InoxExprType = typeOf[inox.trees.Expr]

  protected[macros] object TreeExtractors {
    object Tree {
      def unapply(t: Tree): Option[OpChainTree] = t match {
        case Leaf(leaf) => Some(leaf)
        case Node(node) => Some(node)
        case _          => None
      }
    }

    object Leaf {
      def unapply(t: Tree): Option[OpChainLeaf] = t match {
        case q"$expr.${ Rel(op) }($proof)" => Some(OpChainLeaf(expr, op, proof))
        case _                             => None
      }
    }

    object Node {
      def unapply(t: Tree): Option[OpChainNode] = t match {
        case q"${ Tree(prev) }.|(${ Tree(next) })" => Some(OpChainNode(prev, next))
        case _                                     => None
      }
    }

    object Chain {
      def unapply(t: Tree): Option[OpChain] = t match {
        case q"${ Tree(root) }.|(${ Typed(expr, tpe) })" if tpe <:< InoxExprType => Some(OpChain(root, expr, t.pos))
        case _ => None
      }
    }

    object Typed {
      def unapply(t: Tree): Option[(Tree, Type)] = try {
        val tpe = if (t.tpe != null) t.tpe else c.typecheck(t, c.TERMmode, WildcardType, false, false, true).tpe
        Some((t, tpe))
      } catch {
        case ex: TypecheckException => None
      }
    }
  }

  // must be use by inline suggest only
  protected[macros] lazy val enclosingOpChain: OpChain = pathToMacro.foldRight(Option.empty[OpChain]) {
    case (_, found @ Some(_))             => found
    case (TreeExtractors.Chain(chain), _) => Some(chain)
    case _                                => None
  } get

  protected[macros] lazy val enclosingOpSegment: OpChainSegment = {
    def findMacroLeaf(optree: OpChainTree): Option[OpChainLeaf] = optree match {
      case leaf @ OpChainLeaf(_, _, proof) if proof.pos == c.macroApplication.pos => Some(leaf)
      case OpChainNode(prev, next) => findMacroLeaf(prev) orElse findMacroLeaf(next)
      case _ => None
    }

    def traverse(optree: OpChainTree): Option[OpChainNode] = optree match {
      case node @ OpChainNode(prev, next) => traverse(prev) orElse traverse(next) orElse { findMacroLeaf(prev) map (_ => node) }
      case _                              => None
    }

    traverse(enclosingOpChain.root) getOrElse enclosingOpChain
  }
}