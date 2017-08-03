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
      case (name, sugg) =>
        util.Try(synthesizeTopLevel(expr, sugg)) map (synthed => SynthesizedSuggestion(name, escapeProperly(codeGen.generateScalaCode(synthed)))) match {
          case util.Success(synthsugg) => Some(synthsugg)
          case util.Failure(error)     => println(error); None
        }
    }
  }

  type ASTContext = (ScalaAST, ScalaAST, ScalaAST) => ScalaAST

  def inlineSuggest(lhs: Expr, op: theory.relations.Rel, rhs: Expr)(contextForLHS: ASTContext, contextForRHS: ASTContext): Seq[SynthesizedSuggestion] = {
    val codeGen = new NaiveGenerator

    val lhsSuggs = analyse(lhs, Map.empty, Map.empty)._1 map { case (name, sugg) => (name, contextForLHS, sugg) }
    val rhsSuggs = analyse(rhs, Map.empty, Map.empty)._1 map { case (name, sugg) => (name, contextForRHS, sugg) }

    val sidedSuggs = lhsSuggs ++ rhsSuggs

    sidedSuggs flatMap {
      case (name, ctx, sugg) =>
        util.Try(synthesizeInner(sugg)) map {
          case (res, proof, sugg) => SynthesizedSuggestion(name, escapeProperly(codeGen.generateScalaCode(ctx(res, proof, sugg))))
        } match {
          case util.Success(synthsugg) => Some(synthsugg)
          case util.Failure(error)     => println(error); None
        }
    }
  }

  private def suggestTopLevel(expr: Expr): Seq[NamedTopLevelSuggestion] = expr match {
    case Not(Not(e)) =>
      Seq((s"Negate twice", NegateTwice))

    case And(exprs) =>
      Seq((s"Split cases", FixVariable))

    case Forall(v :: vds, body) =>
      analyseForall(v, body)

    case Implies(hyp, body) =>
      Seq((s"Assume hypothesis", AssumeHypothesis))

    case _: LessThan | _: LessEquals | _: Equals | _: GreaterEquals | _: GreaterThan =>
      Seq((s"Chain", ToChain))

    case _ => Seq()
  }
}

object Assistant {
  def apply(thry: AssistedTheory, ctx: ReflectedContext): Assistant { val theory: thry.type } = new Assistant {
    override val theory: thry.type = thry
    override val reflectedContext: ReflectedContext = ctx
  }
}