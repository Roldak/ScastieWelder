package scastie.welder.core

import welder._
import inox._
import inox.trees._
import scastie.welder._
import scala.meta._

trait Assistant
    extends Suggestions
    with Analysers {

  val theory: NTheory

  case class Result(proof: theory.Proof, expression: Expr)
  case class StructuralInductionHypothesis(constr: Identifier, expr: Expr, hyp: Expr => theory.Attempt[Result], vars: Seq[Variable])

  def suggest(expr: Expr): Seq[NamedSuggestion] = suggestTopLevel(expr)

  private def suggestTopLevel(expr: Expr): Seq[NamedSuggestion] = expr match {
    case Not(Not(e)) =>
      Seq((s"Negate twice", NegateTwice))

    case And(exprs) =>
      Seq((s"Split cases", FixVariable))

    case Forall(v :: vds, body) =>
      //val ret = s"""forallI(\\\"${v.id.name}\\\" :: ${v.tpe}) { v => suggest(${if (vds.isEmpty) body else Forall(vds, body)}) }"""
      Seq((s"Fix variable ${v}", FixVariable))

    case Implies(hyp, body) => 
      Seq((s"Assume hypothesis", AssumeHypothesis))

    case _ => suggestInner(expr)
  }
  
  private def suggestInner(expr: Expr): Seq[NamedSuggestion] = {
    analyse(expr, Map.empty, Map.empty)._1
  }
}

object Assistant {
  def fromInterface(i: Interface): Assistant { val theory: i.theory.type } = new Assistant {
    override val theory: i.theory.type = i.theory
  }
}