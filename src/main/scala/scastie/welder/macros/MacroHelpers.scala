package scastie.welder.macros

import scala.reflect.macros.blackbox.Context

trait MacroHelpers {
  val c: Context
  
  import c.universe._

  object StatefulTraverser {
    trait Actionner[T] {
      def one(tree: Tree, state: T): T
      def some(trees: Seq[Tree], state: T)(merge: Seq[T] => T): T
      def children(tree: Tree, state: T)(merge: Seq[T] => T): T
    }

    def apply[State](visitor: PartialFunction[(Tree, State, Actionner[State]), State]): (Tree, State) => State = {
      class MyTraverser extends Traverser {
        var state: State = _

        private val actionner = new Actionner[State] {
          override def one(tree: Tree, st: State): State = {
            val savedState = state
            state = st
            traverse(tree)
            val res = state
            state = savedState
            res
          }

          override def some(trees: Seq[Tree], st: State)(merge: Seq[State] => State): State = merge(trees map (one(_, st)))
          override def children(tree: Tree, st: State)(merge: Seq[State] => State): State = some(tree.children, st)(merge)
        }

        override def traverse(t: Tree): Unit = {
          if (visitor.isDefinedAt(t, state, actionner)) {
            state = visitor(t, state, actionner)
          }
        }
      }

      val traverser = new MyTraverser

      (tree: Tree, initialState: State) => {
        traverser.state = initialState
        traverser.traverse(tree)
        traverser.state
      }
    }
  }

}