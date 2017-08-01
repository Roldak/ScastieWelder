package scastie.welder.macros

import scala.reflect.macros.blackbox.Context

trait ContextAnalysis { self: Macros =>
  val c: Context

  import c.universe._

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

  protected[macros] trait OpChainSegment {
    def lhs: Tree
    def proof: Tree
    def rhs: Tree
  }
  
  protected[macros] object OpChainSegment {
    def unapply(x: OpChainSegment): Option[(Tree, Tree, Tree)] = Some((x.lhs, x.proof, x.rhs))
  }

  protected[macros] sealed abstract class OpChainTree {
    def leftMost: OpChainLeaf = this match {
      case OpChainNode(prev, next) => prev.leftMost
      case leaf: OpChainLeaf       => leaf
    }
    
    def rightMost: OpChainLeaf = this match {
      case OpChainNode(prev, next) => next.rightMost
      case leaf: OpChainLeaf       => leaf
    }
  }

  protected[macros] case class OpChainNode(prev: OpChainTree, next: OpChainTree) extends OpChainTree with OpChainSegment {
    override def lhs = prev.rightMost.expr
    override def proof = prev.rightMost.proof
    override def rhs = next.leftMost.expr
  }

  protected[macros] case class OpChainLeaf(expr: Tree, proof: Tree) extends OpChainTree

  protected[macros] case class OpChain(root: OpChainTree, expr: Tree) extends OpChainSegment {
    override def lhs = root.rightMost.expr
    override def proof = root.rightMost.proof
    override def rhs = expr
  }

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
        case q"$expr.==|($proof)" => Some(OpChainLeaf(expr, proof))
        case _                    => None
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
        case q"${ Tree(root) }.|($expr)" => Some(OpChain(root, expr))
        case _                           => None
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
    def traverse(optree: OpChainTree): Option[OpChainNode] = optree match {
      case node @ OpChainNode(OpChainLeaf(_, proof), next) if proof.pos == c.macroApplication.pos => Some(node)
      case OpChainNode(prev, next) => traverse(prev) orElse traverse(next)
      case _ => None
    }
    traverse(enclosingOpChain.root) getOrElse enclosingOpChain
  }
}