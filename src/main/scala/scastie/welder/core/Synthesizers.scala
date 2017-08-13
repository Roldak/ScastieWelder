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
    def unapply(t: Any): Option[ScalaAST] = reflectedContext.get(t)
  }

  private def synthesizeValDef(vd: trees.ValDef): ScalaAST = (synthesizeType(vd.tpe) `.` "::")(vd.id.name)

  private def synthesizeType(tpe: Type): ScalaAST = tpe match {
    case Reflected(path)                     => path
    case TypeParameter(Reflected(id), flags) => Raw("TypeParameter")(id, Raw(flags.toString))
    case FunctionType(from, to)              => (synthesizeType(to) `.` "=>:")(Tuple(from map synthesizeType))
    case TupleType(tps)                      => Raw("T")(tps map synthesizeType)
    case ADTType(Reflected(id), tps)         => Raw("T")(id)(tps map synthesizeType)
    case _                                   => throw new SynthesisError(s"Could not synthesize type ${tpe}")
  }

  private def synthesizeExpr(expr: Expr): ScalaAST = {
    def synthesizeInfixOp(lhs: Expr, op: String, rhs: Expr): ScalaAST = (synthesizeExpr(lhs) `.` op)(synthesizeExpr(rhs))

    expr match {
      case Reflected(path) => path
      case Variable(id, tpe, flags) => Raw(id.name)
      case Forall(vds, body) => Raw("forall")(vds map synthesizeValDef)(Function(vds map (_.id.name), synthesizeExpr(body)))
      case Implies(hyp, concl) => synthesizeInfixOp(hyp, "==>", concl)
      case Equals(lhs, rhs) => synthesizeInfixOp(lhs, "===", rhs)
      case And(Seq(lhs, rhs)) => synthesizeInfixOp(lhs, "&&", rhs)
      case And(exprs) => Raw("And")(exprs map synthesizeExpr)
      case Or(Seq(lhs, rhs)) => synthesizeInfixOp(lhs, "||", rhs)
      case Or(exprs) => Raw("Or")(exprs map synthesizeExpr)
      case Application(callee, args) => synthesizeExpr(callee)(args map synthesizeExpr)
      case FunctionInvocation(Reflected(id), tps, args) => Raw("E")(id)(tps map synthesizeType)(args map synthesizeExpr)
      case ADT(adt, args) => synthesizeType(adt)(args map synthesizeExpr)
      case ADTSelector(adt, Reflected(sel)) => (synthesizeExpr(adt) `.` "getField")(sel)
      case IfExpr(cond, then, elz) => Raw("ite")(synthesizeExpr(cond), synthesizeExpr(then), synthesizeExpr(elz))
      case IsInstanceOf(expr, tpe) => (synthesizeExpr(expr) `.` "isInstOf")(synthesizeType(tpe))
      case AsInstanceOf(expr, tpe) => (synthesizeExpr(expr) `.` "asInstOf")(synthesizeType(tpe))
      case _ => throw new SynthesisError(s"Could not synthesize expression ${expr} (${expr.getClass})")
    }
  }

  private def synthesizeProof(proof: Proof): ScalaAST = proof match {
    case Reflected(path)             => path
    case Var(id)                     => Raw(id)
    case Axiom(theorem)              => ???
    case ImplI(id, hyp, concl)       => Raw("implI")(synthesizeExpr(hyp))(Function(Seq(id), synthesizeProof(concl)))
    case ImplE(impl, hyp)            => Raw("implE")(synthesizeProof(impl))(Function(Seq("goal"), (Raw("goal") `.` "by")(synthesizeProof(hyp))))
    case ForallI(v, body)            => Raw("forallI")(synthesizeValDef(v))(Function(Seq(v.id.name), synthesizeProof(body)))
    case ForallE(quantified, value)  => Raw("forallE")(synthesizeProof(quantified))(synthesizeExpr(value))
    case AndI(proofs)                => Raw("andI")(proofs map synthesizeProof)
    case AndE(cunj, parts, body)     => Block(Seq(ValDef(Unapply(Raw("Seq"), parts), Ascript(Raw("andE")(synthesizeProof(cunj)), Raw("Seq[Theorem]"))), synthesizeProof(body)))
    case OrI(alternatives, thm)      => Raw("orI")(alternatives map synthesizeExpr)(Function(Seq("goal"), (Raw("goal") `.` "by")(synthesizeProof(thm))))
    case OrE(disj, concl, id, cases) => ???
    case Prove(expr, hyps)           => Raw("prove")(synthesizeExpr(expr) +: (hyps map synthesizeProof))
    case Let(named, id, body)        => Block(Seq(ValDef(id, synthesizeProof(named)), synthesizeProof(body)))
  }

  def synthesizeTopLevel(expr: Expr, sugg: TopLevelSuggestion): ScalaAST = {
    def suggest(expr: Expr): ScalaAST = Raw("suggest")(synthesizeExpr(expr))
    def inlineSuggest: ScalaAST = Raw("suggest")

    sugg match {
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
          Raw("forallI")(synthesizeValDef(v))(Function(Seq(v.id.name), suggest(body)))

        case Forall(v +: vs, body) =>
          Raw("forallI")(synthesizeValDef(v))(Function(Seq(v.id.name), suggest(Forall(vs, body))))
      }

      case StructuralInduction =>
        val (v, body) = expr match {
          case Forall(Seq(v), body)  => (v, body)
          case Forall(v +: vs, body) => (v, Forall(vs, body))
        }

        val cases = ADTDeconstructable.cases(v.tpe.asInstanceOf[ADTType]) map {
          case (Reflected(constrId), expr, vars) => Case(
            Unapply(Raw("C"), "constr" +: (vars map (_.id.name))),
            Some((Raw("constr") `.` "==")(constrId)),
            suggest(exprOps.replaceFromSymbols(Map(v -> expr), body)))
        }

        Raw("structuralInduction")(Function(Seq(ValDecl(v.id.name, Some(Raw("Expr")))), synthesizeExpr(body)), synthesizeValDef(v))(
          PartialFunction(Seq(Case(Unapply(Raw(""), Seq("ihs", "goal")), None, Match(Raw("ihs") `.` "expression", cases)))))

      case AssumeHypothesis => expr match {
        case Implies(hyp, body) =>
          Raw("implI")(synthesizeExpr(hyp))(Function(Seq("thm"), suggest(body)))
      }

      case ToChain => expr match {
        case Equals(lhs, rhs) => ((synthesizeExpr(lhs) `.` "==|")(inlineSuggest) `.` "|")(synthesizeExpr(rhs))
      }
    }
  }

  def synthesizeInner(sugg: InnerSuggestion): (ScalaAST, ScalaAST, ScalaAST) = {
    def inlineSuggest: ScalaAST = Raw("suggest")

    sugg match {
      case RewriteSuggestion(_, res, proof) =>
        (synthesizeExpr(res), synthesizeProof(proof.proof), inlineSuggest)
    }
  }
}