package scastie.welder.core

import welder._
import inox._
import inox.trees._
import scastie.welder._
import scastie.welder.codegen._

case class SynthesizedSuggestion(title: String, code: String)

trait Assistant
    extends Suggestions
    with Analysers
    with Synthesizers {

  val theory: AssistedTheory
  val codeGen: ScalaCodeGenerator

  case class Result(proof: theory.Proof, expression: Expr)
  case class StructuralInductionHypothesis(constr: Identifier, expr: Expr, hyp: Expr => theory.Attempt[Result], vars: Seq[Variable])

  private def resultExprOf(sugg: InnerSuggestion): Expr = sugg match {
    case RewriteSuggestion(_, res, _) => res
  }

  private def escapeProperly(code: String): String = code.replaceAllLiterally("\"", """\"""").replaceAllLiterally("\n", """\n""")

  def suggest(expr: Expr)(reflCtx: ReflectedContext): Seq[SynthesizedSuggestion] = {
    suggestTopLevel(expr) flatMap {
      case (name, sugg) =>
        util.Try(synthesizeTopLevel(expr, sugg)(reflCtx)) map (synthed => SynthesizedSuggestion(name, escapeProperly(codeGen.generateScalaCode(synthed)))) match {
          case util.Success(synthsugg) => Some(synthsugg)
          case util.Failure(error)     => println(error); None
        }
    }
  }

  type ASTContext = (ScalaAST, ScalaAST, ScalaAST) => ScalaAST

  def inlineSuggest(lhs: Expr, op: theory.relations.Rel, rhs: Expr)(contextForLHS: ASTContext, contextForRHS: ASTContext)(reflCtx: ReflectedContext): Seq[SynthesizedSuggestion] = {
    object Theorem {
      import scastie.welder.codegen.ScalaAST.Implicits._
      
      def unapply(v: Any): Option[(theory.Theorem, ScalaAST => ScalaAST)] = v match {
        case t: theory.Theorem => Some((t, identity))
        case a: theory.Attempt[_] if a.isSuccessful && a.get.isInstanceOf[theory.Theorem] =>
          Some((a.get.asInstanceOf[theory.Theorem], _ `.` "get"))
        case _ => None
      }
    }

    val thms = reflCtx.collect {
      case (path, Theorem(thm, fullPath)) => (codeGen.generateScalaCode(path), Result(theory.Var(codeGen.generateScalaCode(fullPath(path))), thm.expression))
    } toMap

    val ihses = reflCtx.collect {
      case (path, ihs: theory.StructuralInductionHypotheses) =>
        val hyp = { (e: Expr) =>
          val thm = ihs.hypothesis(e)

          // TODO: add structural induction support to Welder Proofs
          thm map (thm => Result(theory.Var(codeGen.generateScalaCode(path)), thm.expression))
        }

        (path.toString, StructuralInductionHypothesis(
          ihs.constructor,
          ihs.expression,
          hyp,
          ihs.variables))
    } toMap

    val lhsSuggs = analyse(lhs, thms, ihses) map { case (name, sugg) => (name, contextForLHS, sugg) }
    val rhsSuggs = analyse(rhs, thms, ihses) map { case (name, sugg) => (name, contextForRHS, sugg) }

    val results = (lhsSuggs ++ rhsSuggs) flatMap {
      case (name, ctx, sugg) =>
        util.Try(synthesizeInner(sugg)(reflCtx)) map {
          case (res, proof, recsugg) => (resultExprOf(sugg), name, codeGen.generateScalaCode(ctx(res, proof, recsugg)))
        } match {
          case util.Success(synthsugg) => Some(synthsugg)
          case util.Failure(error)     => println(error); None
        }
    }

    val uniques = results.groupBy(_._1).mapValues(_.minBy(_._3.size)).toSeq.map {
      case (_, (_, name, code)) => SynthesizedSuggestion(name, code)
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