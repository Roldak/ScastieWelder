package scastie.welder.macros

import scala.reflect.macros.blackbox.Context
import scastie.welder.core.Assistant
import scastie.welder._

class Macros(val c: Context)
    extends MacroHelpers
    with ContextAnalysis {
  
  import c.universe._

  private val preludeOffset = 354 // hardcoded for now

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

    //println("PATH: " + (pathToMacro map (_.getClass.getSimpleName)))
    val values = reachableDefs filter (!_.symbol.isMethod) map (vd => vd.name.toString -> vd.name) toMap
    
    println(values)

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
  
  def suggestInline: Tree = {
    //println("PATH: " + (pathToMacro map (_.getClass.getSimpleName)))
    enclosingOpSegment match {
      case OpChainSegment(lhs, proof, rhs) => println(s"$enclosingOpChain   =>    Segment($lhs, $proof, $rhs)")
    }
    q"trivial"
  }
}