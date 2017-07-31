package scastie.welder.macros

import scala.reflect.macros.blackbox.Context
import scastie.welder.core.Assistant
import scastie.welder._

class Macros(val c: Context) extends MacroHelpers {
  import c.universe._

  private val preludeOffset = 354 // hardcoded for now

  private def typeOf(tree: Tree): Type = c.typecheck(tree, c.TYPEmode).tpe

  private lazy val pathToMacro = IOTraverser[Option[List[Tree]]](None) {
    case (tree, _) if tree.pos == c.macroApplication.pos => Some(Nil)
    case (other, rec)                                    => rec.children(other)(_.find(_ != None).getOrElse(None)).map(other :: _)
  }(c.enclosingPackage).get

  def suggest(expr: Tree): Tree = {
    val Apply(receiver, _) = c.macroApplication

    assert(c.prefix.actualType <:< c.typeOf[AssistedTheory])

    val call = q"""scastie.welder.core.Assistant(${c.prefix}, reflCtx).suggest(expr)"""
    val start = c.macroApplication.pos.start - preludeOffset
    val end = c.macroApplication.pos.end - preludeOffset

    /*
    val testtree = q"""ListA"""
    val typedtree = c.typecheck(testtree, c.TERMmode)
    println(typedtree.equalsStructure(c.typecheck(typedtree, c.TERMmode)))
		*/
    //println(reachableValOrDefs map (_.symbol.typeSignature))

    val values = reachableValOrDefs filter (!_.symbol.isMethod) map (vd => vd.name.toString -> vd.name) toMap

    q"""
	    {
	      import com.olegych.scastie.api._
	      val reflCtx = new scastie.welder.core.ReflectedContext(${values})
	      val expr = $expr
        val str = "<h1>Select suggestion to apply</h1>" + $call.map { case scastie.welder.core.SynthesizedSuggestion(name, replacement) =>
          "<button onclick='ScastieExports.replaceCode(" + $start + ", " + $end + ", \"" + replacement + "\")'>" + name + "</button><br>"
        }.mkString("\n")
	      println(Runtime.write(List(Instrumentation(Position($start, $end), Html(str)))))
	      prove(expr)
	    }
	    """
  }

  private class ValOrDefDefCollector(val before: Tree) extends Traverser {
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

  private object ValOrDefDefCollector {
    def apply(tree: Tree, before: Tree = null): List[ValOrDefDef] = (new ValOrDefDefCollector(before)).findAll(tree)
  }

  private lazy val reachableValOrDefs: Set[ValOrDefDef] = {
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