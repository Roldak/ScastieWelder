package scastie.welder.core

import inox._
import inox.trees._
import scastie.welder.codegen._

trait Synthesizers { self: Assistant =>
  import theory._

  import ScalaAST._
  import ScalaAST.Implicits._

  private def synthesizeValDef(vd: trees.ValDef): ScalaAST = (vd.id.name `.` "::")(synthesizeType(vd.tpe))

  private def synthesizeType(tpe: Type): ScalaAST = tpe match {
    case FunctionType(from, to) => (Tuple(from map synthesizeType) `.` "=>:")(synthesizeType(to))
    case _ => tpe.toString
  }

  private def synthesizeExpr(expr: Expr): ScalaAST = {
    def synthesizeInfixOp(lhs: Expr, op: String, rhs: Expr): ScalaAST = (synthesizeExpr(lhs) `.` op)(synthesizeExpr(rhs))

    expr match {
      case Forall(vds, body)   => Raw("forall")(vds map synthesizeValDef)(Lambda(vds map (_.id.name), synthesizeExpr(body)))
      case Implies(hyp, concl) => synthesizeInfixOp(hyp, "==>", concl)
      case Equals(lhs, rhs)    => synthesizeInfixOp(lhs, "===", rhs)
      case _                   => expr.toString
    }
  }

  private def synthesizeProof(proof: Proof): ScalaAST = proof match {
    case Var(id)                     => Raw(id)
    case Axiom(theorem)              => ???
    case ImplI(id, hyp, concl)       => Raw("implI")(synthesizeExpr(hyp))(Lambda(Seq(id), synthesizeProof(concl)))
    case ImplE(impl, hyp)            => Raw("implE")(synthesizeProof(impl))(Lambda(Seq("goal"), (Raw("goal") `.` "by")(synthesizeProof(hyp))))
    case ForallI(v, body)            => Raw("forallI")(synthesizeValDef(v))(Lambda(Seq(v.id.name), synthesizeProof(body)))
    case ForallE(quantified, value)  => Raw("forallE")(synthesizeProof(quantified))(synthesizeExpr(value))
    case AndI(proofs)                => Raw("andI")(proofs map synthesizeProof)
    case AndE(cunj, parts, body)     => Block(Seq(ValDef(Unapply("", parts), Raw("andE")(synthesizeProof(cunj))), synthesizeProof(body)))
    case OrI(alternatives, thm)      => Raw("orI")(alternatives map synthesizeExpr)(Lambda(Seq("goal"), (Raw("goal") `.` "by")(synthesizeProof(thm))))
    case OrE(disj, concl, id, cases) => ???
    case Prove(expr, hyps)           => Raw("prove")(synthesizeExpr(expr) +: (hyps map synthesizeProof))
    case Let(named, id, body)        => Block(Seq(ValDef(id, synthesizeProof(named)), synthesizeProof(body)))
  }

  def synthesize(expr: Expr, sugg: Suggestion): ScalaAST = {
    def suggest(expr: Expr): ScalaAST = Raw("suggest")(synthesizeExpr(expr))

    sugg match {
      case RewriteSuggestion(subject, res, proof) =>
        ((synthesizeExpr(expr) `.` "==|")(synthesizeProof(proof.proof)) `.` "|")(suggest(res))

      case NegateTwice => expr match {
        case Not(Not(body)) => Raw("notE")(suggest(body))
      }

      case SplitCases => expr match {
        case And(exprs) =>
          val parts = exprs.zipWithIndex map {
            case (e, i) => ValDef(s"part$i", suggest(e))
          }
          Block(parts :+ Raw("andI")(parts.map { case ValDef(ValDecl(name, _), _) => Raw(name) }))
      }

      case FixVariable => expr match {
        case Forall(Seq(v), body) =>
          Raw("forallI")(synthesizeValDef(v))(Lambda(Seq(v.id.name), suggest(body)))

        case Forall(v +: vs, body) =>
          Raw("forallI")(synthesizeValDef(v))(Lambda(Seq(v.id.name), suggest(Forall(vs, body))))
      }

      case StructuralInduction => expr match {
        case Forall(Seq(v), body)  => ???
        case Forall(v +: vs, body) => ???
      }

      case AssumeHypothesis => expr match {
        case Implies(hyp, body) =>
          Raw("implI")(synthesizeExpr(hyp))(Lambda(Seq("thm"), suggest(body)))
      }
    }
  }
}