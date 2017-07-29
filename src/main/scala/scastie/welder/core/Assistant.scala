package scastie.welder.core

import welder._
import inox._
import inox.trees._
import scastie.welder._
import scastie.welder.codegen._

trait Assistant
    extends Suggestions
    with Analysers 
    with Synthesizers {

  val theory: AssistedTheory

  case class Result(proof: theory.Proof, expression: Expr)
  case class StructuralInductionHypothesis(constr: Identifier, expr: Expr, hyp: Expr => theory.Attempt[Result], vars: Seq[Variable])

  def suggest(expr: Expr): Seq[SynthesizedSuggestion] = suggestTopLevel(expr) map {
    sugg => synthesize(new NaiveGenerator)(expr, sugg, e => s"""suggest(\"$e\")""")
  }

  private def suggestTopLevel(expr: Expr): Seq[NamedSuggestion] = expr match {
    case Not(Not(e)) =>
      Seq((s"Negate twice", NegateTwice))

    case And(exprs) =>
      Seq((s"Split cases", FixVariable))

    case Forall(v :: vds, body) =>
      Seq((s"Fix variable ${v.id.name}", FixVariable))

    case Implies(hyp, body) => 
      Seq((s"Assume hypothesis", AssumeHypothesis))

    case _ => suggestInner(expr)
  }
  
  private def suggestInner(expr: Expr): Seq[NamedSuggestion] = {
    analyse(expr, Map.empty, Map.empty)._1
  }
}

object Assistant {
  def fromAssistedTheory(thry: AssistedTheory): Assistant { val theory: thry.type } = new Assistant {
    override val theory: thry.type = thry
  }
}