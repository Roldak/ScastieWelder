package scastie.welder.core

import welder._
import inox._
import inox.trees._
import scastie.welder._
import scastie.welder.codegen._

case class SynthesizedSuggestion(val title: String, val code: String)

trait Assistant
    extends Suggestions
    with Analysers
    with Synthesizers {

  val theory: AssistedTheory
  val reflectedContext: ReflectedContext

  case class Result(proof: theory.Proof, expression: Expr)
  case class StructuralInductionHypothesis(constr: Identifier, expr: Expr, hyp: Expr => theory.Attempt[Result], vars: Seq[Variable])

  private def escapeProperly(code: String): String = code.replaceAllLiterally("\"", """\"""").replaceAllLiterally("\n", """\n""")
  
  def suggest(expr: Expr): Seq[SynthesizedSuggestion] = {
    val codeGen = new NaiveGenerator
    
    suggestTopLevel(expr) flatMap {
      sugg => util.Try(synthesize(expr, sugg._2)) map (synthed => SynthesizedSuggestion(sugg._1, escapeProperly(codeGen.generateScalaCode(synthed)))) match {
        case util.Success(synthsugg) => Some(synthsugg)
        case util.Failure(error) => println(error); None
      }
    }
  }

  private def suggestTopLevel(expr: Expr): Seq[NamedSuggestion] = expr match {
    case Not(Not(e)) =>
      Seq((s"Negate twice", NegateTwice))

    case And(exprs) =>
      Seq((s"Split cases", FixVariable))

    case Forall(v :: vds, body) =>
      analyseForall(v, body)

    case Implies(hyp, body) =>
      Seq((s"Assume hypothesis", AssumeHypothesis))

    case _ => suggestInner(expr)
  }

  private def suggestInner(expr: Expr): Seq[NamedSuggestion] = {
    analyse(expr, Map.empty, Map.empty)._1
  }
}

object Assistant {
  def apply(thry: AssistedTheory, ctx: ReflectedContext): Assistant { val theory: thry.type } = new Assistant {
    override val theory: thry.type = thry
    override val reflectedContext: ReflectedContext = ctx
  }
}