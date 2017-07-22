package scastie.welder.macros

import scala.reflect.macros.blackbox.Context

class Macros(val c: Context) {
  import c.universe._

  def suggest(e: Tree): Tree = {
    val start = c.macroApplication.pos.start
    val end = c.macroApplication.pos.end
    q"""
	    {
	      import com.olegych.scastie.api._
	      println(Runtime.write(List(Instrumentation(Position(${c.literal(start)}, ${c.literal(end)}), Html("<h1>Suggestions:</h1>...")))))
	      $e
	    }
	    """
  }
}