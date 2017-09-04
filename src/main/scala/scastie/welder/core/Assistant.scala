package scastie.welder.core

import welder._
import inox._
import inox.trees._
import scastie.welder._
import scastie.welder.codegen._

trait Assistant
    extends Suggestions
    with Analysers
    with Synthesizers
    with HTMLRendering {

  val theory: AssistedTheory
  val codeGen: ScalaCodeGenerator

  case class Result(proof: theory.Proof, expression: Expr)
  case class StructuralInductionHypothesis(constr: Identifier, expr: Expr, hyp: Expr => theory.Attempt[Result], vars: Seq[Variable])

  case class SynthesizedTopLevelSuggestion(title: String, code: String)
  case class SynthesizedInnerSuggestion(title: String, code: String, subject: Expr, resultExpr: Expr, isLHS: Boolean)

  protected[core] def escapeProperly(code: String): String = code.replaceAllLiterally("\"", """\"""").replaceAllLiterally("\n", """\n""")

  private def tuple2Append[A, B, C](tuple: (A, B), elem: C): (A, B, C) = (tuple._1, tuple._2, elem)

  implicit class ReachableTheorems(ctx: ReflectedContext) {
    import scastie.welder.codegen.ScalaAST.Implicits._
    import theory._

    lazy val reachableTheorems = ctx.collect {
      case (name, thm: Theorem)          => (name, thm)
      case (name, Success(thm: Theorem)) => (name `.` "get", thm)
    }
  }

  def suggest(expr: Expr)(reflCtx: ReflectedContext): Seq[SynthesizedTopLevelSuggestion] = {
    suggestTopLevel(expr) flatMap {
      case (name, sugg) =>
        util.Try(synthesizeTopLevel(expr, sugg)(reflCtx)).map(res => SynthesizedTopLevelSuggestion(name, escapeProperly(codeGen.generateScalaCode(res)))) match {
          case util.Success(synthsugg) => Some(synthsugg)
          case util.Failure(error)     => println(error); None
        }
    }
  }

  type ASTContext = (ScalaAST, ScalaAST, ScalaAST) => ScalaAST

  def inlineSuggest(lhs: Expr, op: theory.relations.Rel, rhs: Expr)(contextForLHS: ASTContext, contextForRHS: ASTContext)(reflCtx: ReflectedContext): Seq[SynthesizedInnerSuggestion] = {
    val thms = reflCtx.reachableTheorems.map {
      case (path, thm) => (codeGen.generateScalaCode(path), Result(theory.Axiom(thm), thm.expression))
    }.toMap

    val ihses = reflCtx.collect {
      case (path, ihs: theory.StructuralInductionHypotheses) =>
        def hyp(e: Expr) = ihs.hypothesis(e) map (thm => Result(theory.SIHypothesis(ihs, e), thm.expression))
        val sih = StructuralInductionHypothesis(ihs.constructor, ihs.expression, hyp, ihs.variables)
        (codeGen.generateScalaCode(path), sih)
    }.toMap

    def buildSuggestion(side: Expr, otherSide: Expr, ctx: ASTContext): NamedInnerSuggestion => Seq[(String, ASTContext, Expr, Expr, String)] = {
      case (name, sugg @ RewriteSuggestion(subjExpr, resultExpr, _)) =>
        util.Try(synthesizeInner(side, otherSide, sugg)(reflCtx)) map {
          case (res, proof, recsugg) => (name, ctx, subjExpr, resultExpr, codeGen.generateScalaCode(ctx(res, proof, recsugg)))
        } match {
          case util.Success(synthsugg) => Seq(synthsugg)
          case util.Failure(error)     => println(error); Seq()
        }
    }

    val lhsSuggs = analyse(lhs, thms ++ findInductiveHypothesisApplication(lhs, ihses)).flatMap(buildSuggestion(lhs, rhs, contextForLHS))
    val rhsSuggs = analyse(rhs, thms ++ findInductiveHypothesisApplication(rhs, ihses)).flatMap(buildSuggestion(rhs, lhs, contextForRHS))

    val uniques = (lhsSuggs ++ rhsSuggs).groupBy(x => (x._2, x._4)).mapValues(_.minBy(_._5.size)).toSeq.map {
      case (_, (name, ctx, subj, res, code)) => SynthesizedInnerSuggestion(name, code, subj, res, ctx eq contextForLHS)
    }

    uniques
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
  def apply(thry: AssistedTheory, cg: ScalaCodeGenerator): Assistant { val theory: thry.type } = new Assistant {
    override val theory: thry.type = thry
    override val codeGen: ScalaCodeGenerator = cg
  }
}