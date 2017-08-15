package scastie.welder.core

import inox._
import inox.trees._
import scastie.welder.codegen._
import scastie.welder.utils.ExprOps
import scala.annotation.tailrec

trait Synthesizers extends ExprOps { self: Assistant =>
  import theory._

  import ScalaAST._
  import ScalaAST.Implicits._
  import scastie.welder.Constants._

  class SynthesisError(val msg: String) extends RuntimeException(msg)

  private val isNotWildcard = (x: String) => x != "_"

  private object BasicNamer {
    def apply(id: String): Int => String = i =>
      if (i == 0) id
      else if (i == 1) s"${id(0)}"
      else s"${id}_${i - 1}"
  }

  private def mergeWhen[T](pattern: Seq[T], values: Seq[T])(f: T => Boolean): Seq[T] = {
    def inner(ps: Seq[T], vs: Seq[T]): Seq[T] = (ps, vs) match {
      case (p +: ps, v +: vs) if f(p) => v +: inner(ps, vs)
      case (p +: ps, vs) if f(p)      => throw new IllegalArgumentException("Pattern must have at most 'values.size' elements to replace")
      case (p +: ps, vs)              => p +: inner(ps, vs)
      case (_, _)                     => Seq()
    }

    inner(pattern, values)
  }

  private case class Synthesizer(reflectedContext: ReflectedContext) {
    @tailrec
    private def chooseName(namer: Int => String, i: Int = 0): String = {
      val name = namer(i)
      if (reflectedContext.existsPath(Raw(name))) chooseName(namer, i + 1)
      else name
    }

    private def updated(value: Any, name: ScalaAST): Option[Synthesizer] =
      if (reflectedContext.existsPath(name)) None
      else Some(copy(reflectedContext = reflectedContext.updated(name, value)))

    private def updatedVar(value: Any, namer: Int => String): (String, Synthesizer) = {
      val name = chooseName(namer)
      (name, copy(reflectedContext = reflectedContext.updated(Raw(name), value)))
    }

    private def updatedVars(elems: Seq[(Any, Int => String)]): (Seq[String], Synthesizer) = elems.foldLeft((Seq.empty[String], this)) {
      case ((names, synth), (value, namer)) =>
        val (name, newSynth) = synth.updatedVar(value, namer)
        (names :+ name, newSynth)
    }

    private def updatedVarsThen[T](elems: Seq[(Any, Int => String)])(f: (Seq[String], Synthesizer) => T): T = f.tupled(updatedVars(elems))

    private lazy val rewriteRules = reflectedContext.collect {
      case (name, rule: RewriteRule) => (name, rule)
    }

    private object Reflected {
      def unapply(t: Any): Option[ScalaAST] = reflectedContext.get(t)
    }

    private object Rewritten {
      def unapply(e: Expr): Option[ScalaAST] = {
        rewriteRules.flatMap {
          case (name, rule) =>
            unify(rule.pattern, e, rule.holes.toSet) map { subst =>
              name(rule.holes.map(subst).map(synthesizeExpr))
            }
        } reduceOption ((a, b) => if (a.toString.size < b.toString.size) a else b)
      }
    }

    private def suggest(expr: Expr): ScalaAST = Raw("suggest")(synthesizeExpr(expr))
    private def inlineSuggest: ScalaAST = Raw("suggest")

    private def synthesizeValDef(vd: trees.ValDef): ScalaAST = (synthesizeType(vd.tpe) `.` "::")(vd.id.name)

    private def synthesizeType(tpe: Type): ScalaAST = tpe match {
      case Reflected(name)                     => name
      case TypeParameter(Reflected(id), flags) => Raw("TypeParameter")(id, Raw(flags.toString))
      case FunctionType(from, to)              => (synthesizeType(to) `.` "=>:")(Tuple(from map synthesizeType))
      case TupleType(tps)                      => Raw("T")(tps map synthesizeType)
      case ADTType(Reflected(id), tps)         => Raw("T")(id)(tps map synthesizeType)
      case _                                   => throw new SynthesisError(s"Could not synthesize type ${tpe}")
    }

    private def synthesizeExpr(expr: Expr): ScalaAST = {
      def synthesizeInfixOp(lhs: Expr, op: String, rhs: Expr): ScalaAST = (synthesizeExpr(lhs) `.` op)(synthesizeExpr(rhs))

      expr match {
        case Reflected(name) => name
        case Rewritten(ast) => ast
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

    private def synthesizeAndE(cunj: Proof, parts: Seq[theory.MetaIdentifier], body: Proof): ScalaAST = {
      val shortened: Option[ScalaAST] = if (parts.count(isNotWildcard) == 1) {
        val idx = parts.indexWhere(isNotWildcard)
        updated(Var(parts(idx)), Raw("andE")(synthesizeProof(cunj))(IntLiteral(idx))).map(_.synthesizeProof(body))
      } else None

      shortened.getOrElse {
        updatedVarsThen(parts.filter(isNotWildcard).map(id => (Var(id), BasicNamer(id)))) { (vars, rec) =>
          Block(Seq(ValDef(Unapply(Raw("Seq"), mergeWhen(parts, vars)(isNotWildcard)), Ascript(Raw("andE")(synthesizeProof(cunj)), Raw("Seq[Theorem]"))),
            rec.synthesizeProof(body)))
        }
      }
    }

    private def synthesizeProof(proof: Proof): ScalaAST = proof match {
      case Reflected(name)             => name
      case Var(id)                     => Raw(id)
      case Axiom(theorem)              => ???
      case ImplI(id, hyp, concl)       => Raw("implI")(synthesizeExpr(hyp))(Function(Seq(id), synthesizeProof(concl)))
      case ImplE(impl, hyp)            => Raw("implE")(synthesizeProof(impl))(Function(Seq("goal"), (Raw("goal") `.` "by")(synthesizeProof(hyp))))
      case ForallI(v, body)            => Raw("forallI")(synthesizeValDef(v))(Function(Seq(v.id.name), synthesizeProof(body)))
      case ForallE(quantified, value)  => Raw("forallE")(synthesizeProof(quantified))(synthesizeExpr(value))
      case AndI(proofs)                => Raw("andI")(proofs map synthesizeProof)
      case AndE(cunj, parts, body)     => synthesizeAndE(cunj, parts, body)
      case OrI(alternatives, thm)      => Raw("orI")(alternatives map synthesizeExpr)(Function(Seq("goal"), (Raw("goal") `.` "by")(synthesizeProof(thm))))
      case OrE(disj, concl, id, cases) => ???
      case Prove(expr, hyps)           => Raw("prove")(synthesizeExpr(expr) +: (hyps map synthesizeProof))
      case Let(named, id, body)        => Block(Seq(ValDef(id, synthesizeProof(named)), synthesizeProof(body)))
    }

    def synthesizeTopLevel(expr: Expr, sugg: TopLevelSuggestion): ScalaAST = {
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
            case (Reflected(constrId), expr, vars) => updatedVarsThen(vars map (v => (v, BasicNamer(v.id.name)))) { (names, synth) =>
              Case(
                Unapply(Raw("C"), "constr" +: names),
                Some((Raw("constr") `.` "==")(constrId)),
                synth.suggest(exprOps.replaceFromSymbols(Map(v -> expr), body)))
            }
          }

          Raw("structuralInduction")(Function(Seq(ValDecl(v.id.name, Some(Raw("Expr")))), synthesizeExpr(body)), synthesizeValDef(v))(
            PartialFunction(Seq(Case(Unapply(Raw(""), Seq("ihs", "goal")), None, Match(Raw("ihs") `.` "expression", cases)))))

        case AssumeHypothesis => expr match {
          case Implies(hyp, body) =>
            Raw("implI")(synthesizeExpr(hyp))(Function(Seq("thm"), suggest(body)))
        }

        case ToChain => expr match {
          case Equals(lhs, rhs) => ((synthesizeExpr(lhs) `.` Rel.EQ)(inlineSuggest) `.` Rel.CONCAT)(synthesizeExpr(rhs))
        }
      }
    }

    def synthesizeInner(sugg: InnerSuggestion): (ScalaAST, ScalaAST, ScalaAST) = {
      sugg match {
        case RewriteSuggestion(_, res, proof) =>
          (synthesizeExpr(res), synthesizeProof(proof.proof), inlineSuggest)
      }
    }
  }

  def synthesizeTopLevel(expr: Expr, sugg: TopLevelSuggestion)(ctx: ReflectedContext): ScalaAST = Synthesizer(ctx).synthesizeTopLevel(expr, sugg)
  def synthesizeInner(sugg: InnerSuggestion)(ctx: ReflectedContext): (ScalaAST, ScalaAST, ScalaAST) = Synthesizer(ctx).synthesizeInner(sugg)
}