package scastie.welder.core

import inox._
import inox.trees._
import scastie.welder.codegen._

case class SynthesizedSuggestion(val title: String, val code: String)

trait Synthesizers { self: Assistant =>
  import theory._

  import ScalaAST._
  import ScalaAST.Implicits._
  
  private def escapeProperly(code: String): String = code.replaceAllLiterally("\"", """\"""").replaceAllLiterally("\n", """\n""")

  private def synthesizeProof(proof: Proof): ScalaAST = proof match {
    case Var(id)                     => Raw(id)
    case Axiom(theorem)              => ???
    case ImplI(id, hyp, concl)       => Raw("implI")(hyp.toString)(Lambda(Seq(id), synthesizeProof(concl)))
    case ImplE(impl, hyp)            => Raw("implE")(synthesizeProof(impl))(Lambda(Seq("goal"), (Raw("goal") `.` "by")(synthesizeProof(hyp))))
    case ForallI(v, body)            => Raw("forallI")((v.id.name `.` "::")(v.tpe.toString))(Lambda(Seq(v.id.name), synthesizeProof(body)))
    case ForallE(quantified, value)  => Raw("forallE")(synthesizeProof(quantified))(value.toString)
    case AndI(proofs)                => Raw("andI")(proofs map synthesizeProof)
    case AndE(cunj, parts, body)     => Block(Seq(ValDef(Unapply("", parts), Raw("andE")(synthesizeProof(cunj))), synthesizeProof(body)))
    case OrI(alternatives, thm)      => Raw("orI")(alternatives map (_.toString))(Lambda(Seq("goal"), (Raw("goal") `.` "by")(synthesizeProof(thm))))
    case OrE(disj, concl, id, cases) => ???
    case Prove(expr, hyps)           => Raw("prove")((expr.toString: ScalaAST) +: (hyps map synthesizeProof))
    case Let(named, id, body)        => Block(Seq(ValDef(id, synthesizeProof(named)), synthesizeProof(body)))
  }

  def synthesize(codegen: ScalaCodeGenerator)(expr: Expr, sugg: NamedSuggestion, recursiveSuggest: (Expr) => String): SynthesizedSuggestion = {
    val ast = sugg._2 match {
      case RewriteSuggestion(subject, res, proof) =>
        ((expr.toString `.` "==|")(synthesizeProof(proof.proof)) `.` "|")(Raw(recursiveSuggest(res)))

      case NegateTwice => expr match {
        case Not(Not(body)) => Raw("notE")(Raw(recursiveSuggest(body)))
      }

      case SplitCases => expr match {
        case And(exprs) =>
          val parts = exprs.zipWithIndex map {
            case (e, i) => ValDef(s"part$i", Raw(recursiveSuggest(e)))
          }
          Block(parts :+ Raw("andI")(parts.map { case ValDef(ValDecl(name, _), _) => Raw(name) }))
      }

      case FixVariable => expr match {
        case Forall(Seq(v), body) =>
          Raw("forallI")((v.id.name `.` "::")(v.tpe.toString))(Lambda(Seq(v.id.name), Raw(recursiveSuggest(body))))

        case Forall(v +: vs, body) =>
          Raw("forallI")((v.id.name `.` "::")(v.tpe.toString))(Lambda(Seq(v.id.name), Raw(recursiveSuggest(Forall(vs, body)))))
      }

      case StructuralInduction => expr match {
        case Forall(Seq(v), body)  => ??? // TODO
        case Forall(v +: vs, body) => ??? // TODO
      }

      case AssumeHypothesis => expr match {
        case Implies(hyp, body) =>
          Raw("implI")(hyp.toString)(Lambda(Seq("thm"), Raw(recursiveSuggest(body))))
      }
    }
    SynthesizedSuggestion(sugg._1, escapeProperly(codegen.generateScalaCode(ast)))
  }
}