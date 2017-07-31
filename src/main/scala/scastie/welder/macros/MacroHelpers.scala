package scastie.welder.macros

import scala.reflect.macros.blackbox.Context

trait MacroHelpers {
  val c: Context

  import c.universe._

  object IOTraverser {
    trait Actionner[T, U] {
      def one(tree: Tree, input: T): U
      def some(trees: Seq[Tree], input: T)(implicit merge: Seq[U] => U): U
      def children(tree: Tree, input: T)(implicit merge: Seq[U] => U): U
    }

    class UnitActionnerDelegate[U](val actionner: Actionner[Unit, U]) {
      def one(tree: Tree): U = actionner.one(tree, ())
      def some(trees: Seq[Tree])(implicit merge: Seq[U] => U): U = actionner.some(trees, ())
      def children(tree: Tree)(implicit merge: Seq[U] => U): U = actionner.children(tree, ())
    }

    def apply[In, Out](defaultOutput: Out)(visitor: PartialFunction[(Tree, In, Actionner[In, Out]), Out]): (Tree, In) => Out = {
      class MyTraverser extends Traverser {
        var input: In = _
        var output: Out = _

        private val actionner = new Actionner[In, Out] {
          override def one(tree: Tree, st: In): Out = {
            val savedInput = input
            input = st
            traverse(tree)
            input = savedInput
            output
          }

          override def some(trees: Seq[Tree], st: In)(implicit merge: Seq[Out] => Out): Out = merge(trees map (one(_, st)))
          override def children(tree: Tree, st: In)(implicit merge: Seq[Out] => Out): Out = some(tree.children, st)(merge)
        }

        override def traverse(t: Tree): Unit = {
          output =
            if (visitor.isDefinedAt(t, input, actionner)) visitor(t, input, actionner)
            else defaultOutput
        }
      }

      val traverser = new MyTraverser

      (tree: Tree, initialInput: In) => {
        traverser.input = initialInput
        traverser.traverse(tree)
        traverser.output
      }
    }

    def apply[Out](defaultOutput: Out)(visitor: PartialFunction[(Tree, UnitActionnerDelegate[Out]), Out]): Tree => Out = {
      val traverser = apply[Unit, Out](defaultOutput) {
        case (tree, _, actionner) => visitor(tree, new UnitActionnerDelegate(actionner))
      }

      (tree: Tree) => {
        traverser(tree, ())
      }
    }
  }

}