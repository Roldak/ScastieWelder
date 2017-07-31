package scastie.welder.macros

import scala.reflect.macros.blackbox.Context

trait MacroHelpers {
  val c: Context

  import c.universe._

  object StatefulTraverser {
    trait Actionner[T, U] {
      def one(tree: Tree, state: T): U
      def some(trees: Seq[Tree], state: T)(implicit merge: Seq[U] => U): U
      def children(tree: Tree, state: T)(implicit merge: Seq[U] => U): U
    }

    class UnitActionnerDelegate[U](val actionner: Actionner[Unit, U]) {
      def one(tree: Tree): U = actionner.one(tree, ())
      def some(trees: Seq[Tree])(implicit merge: Seq[U] => U): U = actionner.some(trees, ())
      def children(tree: Tree)(implicit merge: Seq[U] => U): U = actionner.children(tree, ())
    }

    def apply[InState, OutState](defaultOutState: OutState)(visitor: PartialFunction[(Tree, InState, Actionner[InState, OutState]), OutState]): (Tree, InState) => OutState = {
      class MyTraverser extends Traverser {
        var inState: InState = _
        var outState: OutState = _

        private val actionner = new Actionner[InState, OutState] {
          override def one(tree: Tree, st: InState): OutState = {
            val savedState = inState
            inState = st
            traverse(tree)
            inState = savedState
            outState
          }

          override def some(trees: Seq[Tree], st: InState)(implicit merge: Seq[OutState] => OutState): OutState = merge(trees map (one(_, st)))
          override def children(tree: Tree, st: InState)(implicit merge: Seq[OutState] => OutState): OutState = some(tree.children, st)(merge)
        }

        override def traverse(t: Tree): Unit = {
          outState =
            if (visitor.isDefinedAt(t, inState, actionner)) visitor(t, inState, actionner)
            else defaultOutState
        }
      }

      val traverser = new MyTraverser

      (tree: Tree, initialState: InState) => {
        traverser.inState = initialState
        traverser.traverse(tree)
        traverser.outState
      }
    }

    def apply[OutState](defaultOutState: OutState)(visitor: PartialFunction[(Tree, UnitActionnerDelegate[OutState]), OutState]): Tree => OutState = {
      val traverser = apply[Unit, OutState](defaultOutState) {
        case (tree, _, actionner) => visitor(tree, new UnitActionnerDelegate(actionner))
      }

      (tree: Tree) => {
        traverser(tree, ())
      }
    }
  }

}