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

  protected[macros] lazy val pathToMacro = IOTraverser[Option[List[Tree]]](None) {
    case (tree, _) if tree.pos == c.macroApplication.pos => Some(Nil)
    case (other, rec)                                    => rec.children(other)(_.find(_ != None).getOrElse(None)).map(other :: _)
  }(c.enclosingPackage).get

  protected[macros] lazy val reachableValOrDefs: Set[ValOrDefDef] = {
    case class Input(path: List[Tree], inClosedScope: Boolean) {
      def next = copy(path = path.tail)
      def next(isInClosedScope: Boolean) = copy(path = path.tail, inClosedScope = isInClosedScope)

      def isPrefix(tree: Tree): Boolean = path != Nil && path.head == tree
    }
    type Output = Set[ValOrDefDef]

    implicit def mergeOutputs(outs: Seq[Output]): Output = outs.flatten.toSet

    val traverser = IOTraverser[Input, Output](Set.empty) {
      case (tree, input, rec) if input.isPrefix(tree) => {
        val output = tree match {
          case Template(_, self, body)         => rec.some(body, input.next(false)) ++ ValOrDefDefCollector(tree)
          case DefDef(_, _, _, params, _, rhs) => rec.one(rhs, input.next(true)) ++ params.flatten
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
}