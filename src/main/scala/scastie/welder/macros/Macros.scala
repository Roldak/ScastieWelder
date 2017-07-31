package scastie.welder.macros

import scala.reflect.macros.blackbox.Context
import scastie.welder.core.Assistant
import scastie.welder._

class Macros(val c: Context) extends MacroHelpers {
  import c.universe._

  private val preludeOffset = 354 // hardcoded for now

  private def typeOf(tree: Tree): Type = c.typecheck(tree, c.TYPEmode).tpe

  private lazy val pathToMacro = StatefulTraverser[Option[List[Tree]]] {
    case (tree, _, _) if tree.pos == c.macroApplication.pos => Some(Nil)
    case (other, _, rec)                                    => rec.children(other, None)(_.find(_ != None).getOrElse(None)).map(_.::(other))
  }(c.enclosingPackage, None).get

  def suggest(expr: Tree): Tree = {
    val Apply(receiver, _) = c.macroApplication

    assert(c.prefix.actualType <:< c.typeOf[AssistedTheory])

    val call = q"""scastie.welder.core.Assistant.fromAssistedTheory(${c.prefix}).suggest(expr)"""
    /*
    val testtree = q"""ListA"""
    val typedtree = c.typecheck(testtree, c.TERMmode)
    println(typedtree.equalsStructure(c.typecheck(typedtree, c.TERMmode)))
*/
    val start = c.macroApplication.pos.start - preludeOffset
    val end = c.macroApplication.pos.end - preludeOffset

    println(reachableValOrDefs map (_.symbol))

    q"""
	    {
	      import com.olegych.scastie.api._
	      val expr = $expr
        val str = "<h1>Select suggestion to apply</h1>" + $call.map { case scastie.welder.core.SynthesizedSuggestion(name, replacement) =>
          "<button onclick='ScastieExports.replaceCode(" + $start + ", " + $end + ", \"" + replacement + "\")'>" + name + "</button><br>"
        }.mkString("\n")
	      
	      prove(expr)
	    }
	    """
    //println(Runtime.write(List(Instrumentation(Position($start, $end), Html(str)))))
  }

  private class ValOrDefDefCollector(val before: Tree) extends Traverser {
    private var valdefs: List[ValOrDefDef] = _
    private var stillCollecting = true

    println("BEFORE: " + before)

    def findAll(t: Tree): List[ValOrDefDef] = {
      valdefs = Nil
      super.traverse(t)
      valdefs
    }

    override def traverse(t: Tree): Unit = t match {
      case tree if tree == before =>
        println("helloooooo")
        stillCollecting = false
      case vd: ValOrDefDef if stillCollecting => valdefs ::= vd
      case _                                  =>
    }
  }

  private object ValOrDefDefCollector {
    def apply(tree: Tree, before: Tree = null): List[ValOrDefDef] = (new ValOrDefDefCollector(before)).findAll(tree)
  }

  private lazy val reachableValOrDefs: Set[ValOrDefDef] = {
    // TODO: split StatefulTraverser states in two

    case class State(path: List[Tree], inClosedScope: Boolean, valdefs: Set[ValOrDefDef]) {
      def next: State = copy(path = path.tail)
      def enterClosedScope = copy(inClosedScope = true)
      def withDef(vd: ValOrDefDef): State = copy(valdefs = valdefs + vd)
      def withDefs(vds: Iterable[ValOrDefDef]): State = copy(valdefs = valdefs ++ vds)

      def isPrefix(tree: Tree): Boolean = path != Nil && path.head == tree
    }

    def mergeStates(states: Seq[State]): State = State(Nil, false, states.map(_.valdefs).flatten.toSet)

    val traverser = StatefulTraverser[State] {
      case (tree, state, rec) if state.isPrefix(tree) => {
        val resState = tree match {
          case Template(_, self, body)         => rec.some(body, state.next)(mergeStates) withDefs ValOrDefDefCollector(tree)
          case DefDef(_, _, _, params, _, rhs) => rec.one(rhs, state.next.enterClosedScope) withDefs params.flatten
          case _                               => rec.children(tree, state.next)(mergeStates)
        }
        
        if (state.inClosedScope) {
          resState withDefs ValOrDefDefCollector(tree, tree.children.find(state.next.isPrefix).getOrElse(null))          
        } else { 
          resState
        }
      }
    }

    c.enclosingRun.units.map {
      unit => traverser(unit.body, State(pathToMacro, false, Set.empty)).valdefs
    }.flatten.toSet
  }
}