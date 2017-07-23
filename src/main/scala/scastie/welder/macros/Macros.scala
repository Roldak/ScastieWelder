package scastie.welder.macros

import scala.reflect.macros.blackbox.Context

import scastie.welder.Interface
import scastie.welder.core.Assistant

class Macros(val c: Context) {
  import c.universe._

  private val preludeOffset = 354 // hardcoded for now
  
  def suggest(expr: Tree): Tree = {
    val interface = c.macroApplication.find(_.tpe <:< c.typeOf[Interface]).get
    val call = q"""scastie.welder.core.Assistant.fromInterface($interface).suggest($expr)"""
    
    val start = c.literal(c.macroApplication.pos.start - preludeOffset)
    val end = c.literal(c.macroApplication.pos.end - preludeOffset)
    q"""
	    {
	      import com.olegych.scastie.api._
          val str = "<h1>Select suggestion to apply</h1>" + $call.map { case (name, replacement) => 
            "<button onclick='ScastieExports.replaceCode(" + $start + ", " + $end + ", \"" + replacement + "\")'>" + name + "</button><br>"
          }.mkString("\n")
	      println(Runtime.write(List(Instrumentation(Position($start, $end), Html(str)))))
	      prove($expr)
	    }
	    """
  }
}