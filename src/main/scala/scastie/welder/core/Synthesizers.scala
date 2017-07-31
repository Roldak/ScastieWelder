package scastie.welder.core

import inox._
import inox.trees._
import scastie.welder.codegen._

trait Synthesizers { self: Assistant =>
  import theory._

  import ScalaAST._
  import ScalaAST.Implicits._

  class SynthesisError(val msg: String) extends RuntimeException(msg)

  private object Reflected {
    def unapply(t: Any): Option[String] = reflectedContext.get(t)
  }

  private def synthesizeValDef(vd: trees.ValDef): ScalaAST = (synthesizeType(vd.tpe) `.` "::")(vd.id.name)

  private def synthesizeType(tpe: Type): ScalaAST = tpe match {
    case Reflected(path)             => Raw(path)
    case TypeParameter(id, _)        => throw new SynthesisError(s"Could not synthesize type parameter ${id.name}")
    case FunctionType(from, to)      => (synthesizeType(to) `.` "=>:")(Tuple(from map synthesizeType))
    case ADTType(Reflected(id), tps) => Raw("T")(Raw(id))(tps map synthesizeType)
    case _                           => throw new SynthesisError(s"Could not synthesize type ${tpe}")
  }

  private def synthesizeExpr(expr: Expr): ScalaAST = {
    def synthesizeInfixOp(lhs: Expr, op: String, rhs: Expr): ScalaAST = (synthesizeExpr(lhs) `.` op)(synthesizeExpr(rhs))

    expr match {
      case Reflected(path) => Raw(path)
      case Variable(id, tpe, flags) => Raw(id.name)
      case Forall(vds, body) => Raw("forall")(vds map synthesizeValDef)(Lambda(vds map (_.id.name), synthesizeExpr(body)))
      case Implies(hyp, concl) => synthesizeInfixOp(hyp, "==>", concl)
      case Equals(lhs, rhs) => synthesizeInfixOp(lhs, "===", rhs)
      case And(Seq(lhs, rhs)) => synthesizeInfixOp(lhs, "&&", rhs)
      case And(exprs) => Raw("And")(exprs map synthesizeExpr)
      case Or(Seq(lhs, rhs)) => synthesizeInfixOp(lhs, "||", rhs)
      case Or(exprs) => Raw("Or")(exprs map synthesizeExpr)
      case Application(callee, args) => synthesizeExpr(callee)(args map synthesizeExpr)
      case FunctionInvocation(Reflected(id), tps, args) => Raw("E")(Raw(id))(tps map synthesizeType)(args map synthesizeExpr)
      case _ => throw new SynthesisError(s"Could not synthesize expression ${expr}")
    }
  }

  private def synthesizeProof(proof: Proof): ScalaAST = proof match {
    case Reflected(path)             => Raw(path)
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