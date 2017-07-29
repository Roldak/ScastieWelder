package scastie.welder.macros

import scala.reflect.macros.blackbox.Context
import scastie.welder.core.Assistant
import scastie.welder._

class Macros(val c: Context) {
  import c.universe._

  private val preludeOffset = 354 // hardcoded for now

  private def typeOf(tree: Tree): Type = c.typecheck(tree, c.TYPEmode).tpe

  def suggest(expr: Tree): Tree = {
    val Apply(receiver, _) = c.macroApplication
    
    assert(c.prefix.actualType <:< c.typeOf[AssistedTheory])
    
    val call = q"""scastie.welder.core.Assistant.fromAssistedTheory(${c.prefix}).suggest(expr)"""

    val start = c.macroApplication.pos.start - preludeOffset
    val end = c.macroApplication.pos.end - preludeOffset

    q"""
	    {
	      import com.olegych.scastie.api._
	      val expr = $expr
        val str = "<h1>Select suggestion to apply</h1>" + $call.map { case scastie.welder.core.SynthesizedSuggestion(name, replacement) =>
          "<button onclick='ScastieExports.replaceCode(" + $start + ", " + $end + ", \"" + replacement + "\")'>" + name + "</button><br>"
        }.mkString("\n")
	      println(Runtime.write(List(Instrumentation(Position($start, $end), Html(str)))))
	      prove(expr)
	    }
	    """
  }
}