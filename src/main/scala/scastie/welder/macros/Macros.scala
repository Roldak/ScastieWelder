package scastie.welder.macros

import scala.reflect.macros.blackbox.Context

class Macros(val c: Context) {
  import c.universe._

  private val preludeOffset = 354 // hardcoded for now
  
  def suggest(expr: Tree): Tree = {
    val start = c.macroApplication.pos.start - preludeOffset
    val end = c.macroApplication.pos.end - preludeOffset
    val str = s"""<button onclick='ScastieExports.replaceCode($start, $end, "REPLACED")'>Replace!</button>"""
    q"""
	    {
	      import com.olegych.scastie.api._
	      println(Runtime.write(List(Instrumentation(Position(${c.literal(start)}, ${c.literal(end)}), Html(${c.literal(str)})))))
	      prove($expr)
	    }
	    """
  }
}