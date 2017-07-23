package scastie.welder.core

import welder._
import inox._
import inox.trees._
import scastie.welder.Interface
import scala.meta._

trait Assistant 
	extends Suggestions {
  
  val theory: Theory
  
  def suggest(expr: Expr): Seq[NamedSuggestion] = suggestTopLevel(expr)
  
  private def suggestTopLevel(expr: Expr): Seq[NamedSuggestion] = expr match {
    case Forall(v :: vds, body) => 
      val ret = q"""forallI(${Lit.String(v.id.name)} :: ${v.tpe.toString}) {
        v => suggest(${if (vds.isEmpty) body.toString else Forall(vds, body).toString})
      }"""
      Seq((s"Fix variable ${v}", ret.syntax))
  }
}

object Assistant {
  def fromInterface(i: Interface): Assistant { val theory: i.theory.type } = new Assistant {
    override val theory: i.theory.type = i.theory 
  }
}