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

  private type Namer = Int => String

  private object BasicNamer {
    def apply(id: String): Namer = i =>
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

  private object FlattenedForallE {
    def unapply(p: Proof): Option[(Proof, Seq[Expr])] = p match {
      case ForallE(FlattenedForallE(quantified, values), v) => Some(quantified, values :+ v)
      case ForallE(quantified, v) => Some(quantified, Seq(v))
      case _ => None
    }
  }

  private case class Synthesizer(reflectedContext: ReflectedContext) {
    @tailrec
    private def chooseName(namer: Namer, i: Int = 0): String = {
      val name = namer(i)
      if (reflectedContext.existsPath(Raw(name))) chooseName(namer, i + 1)
      else name
    }

    private def updated(value: Any, name: ScalaAST): Option[Synthesizer] =
      if (reflectedContext.existsPath(name)) None
      else Some(copy(reflectedContext = reflectedContext.updated(name, value)))

    private def updatedVar(value: Any, namer: Namer): (String, Synthesizer) = {
      val name = chooseName(namer)
      (name, copy(reflectedContext = reflectedContext.updated(Raw(name), value)))
    }

    private def updatedVars(elems: Seq[(Any, Namer)]): (Seq[String], Synthesizer) = elems.foldLeft((Seq.empty[String], this)) {
      case ((names, synth), (value, namer)) =>
        val (name, newSynth) = synth.updatedVar(value, namer)
        (names :+ name, newSynth)
    }

    private def updatedVarThen[T](value: Any, namer: Namer)(f: (String, Synthesizer) => T): T = f.tupled(updatedVar(value, namer))
    private def updatedVarsThen[T](elems: Seq[(Any, Namer)])(f: (Seq[String], Synthesizer) => T): T = f.tupled(updatedVars(elems))

    private lazy val rewriteRules = reflectedContext.collect {
      case (name, rule: RewriteRule) => (name, rule)
    }

    private object Reflected {
      def unapply(t: Any): Option[ScalaAST] = reflectedContext.get(t)
      def unapply(t: Theorem): Option[ScalaAST] = reflectedContext.reachableTheorems.find(_._2 == t).map(_._1)
    }

    private object Rewritten {
      def unapply(e: Expr): Option[(ScalaAST, Seq[Expr])] = {
        rewriteRules.flatMap {
          case (name, rule) =>
            unify(rule.pattern, e, rule.holes.toSet) map { subst =>
              (name, rule.holes.map(subst))
            }
        } reduceOption ((a, b) => if (a.toString.size < b.toString.size) a else b)
      }
    }

    private object ExprNamer {
      def apply(fallback: Namer)(expr: Expr): Namer = {
        def inner(expr: Expr, lvl: Int): String = {
          def innerRec(expr: Expr) = inner(expr, lvl - 1)
          def innerRecs(exprs: Iterable[Expr], sep: String = "") = exprs map innerRec mkString sep

          expr match {
            case Reflected(Raw(name)) if lvl == 0 => name

            case Rewritten(Raw(name), exprs) =>
              if (lvl == 0) name
              else s"$name${innerRecs(exprs)}"

            case Variable(id, _, _) if lvl == 0 => id.name

            case FunctionInvocation(id, tps, args) =>
              if (lvl == 0) id.name
              else s"${id.name}${innerRecs(args)}"

            case Equals(lhs, rhs) =>
              if (lvl == 0) "eq"
              else s"${inner(lhs, lvl - 1)}Is${innerRec(rhs)}"

            case And(exprs) =>
              if (lvl == 0) "cunj"
              else s"${innerRecs(exprs, "And")}"

            case Or(exprs) =>
              if (lvl == 0) "disj"
              else s"${innerRecs(exprs, "Or")}"

            case _ => fallback(lvl)
          }
        }

        (x: Int) => inner(expr, x)
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
        case Reflected(name)        => name
        case Rewritten(name, exprs) => name(exprs map synthesizeExpr)

        case Forall(vds, body) => updatedVarsThen(vds.map(v => (v, BasicNamer(v.id.name)))) { (names, synth) =>
          Raw("forall")(vds map synthesizeValDef)(Function(names, synth.synthesizeExpr(body)))
        }

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

    private def synthesizeForallI(vd: trees.ValDef)(f: Synthesizer => ScalaAST): ScalaAST = {
      updatedVarThen(vd, BasicNamer(vd.id.name)) { (name, synth) =>
        Raw("forallI")(synthesizeValDef(vd))(Function(Seq(name), f(synth)))
      }
    }

    private def synthesizeImplI(id: MetaIdentifier, hyp: Expr)(f: (String, Synthesizer) => ScalaAST): ScalaAST = {
      updatedVarThen(Var(id), ExprNamer(BasicNamer(id))(hyp)) { (name, synth) =>
        Raw("implI")(synthesizeExpr(hyp))(Function(Seq(name), f(name, synth)))
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
      case Reflected(name)                 => name
      case Axiom(Reflected(thm))           => thm
      case SIHypothesis(Reflected(ihs), e) => (ihs `.` "hypothesis")(synthesizeExpr(e))

      case ForallI(vd, body)               => synthesizeForallI(vd)(_.synthesizeProof(body))
      case FlattenedForallE(expr, terms)   => Raw("forallE")(synthesizeProof(expr))(terms map synthesizeExpr)
      case ImplI(id, hyp, concl)           => synthesizeImplI(id, hyp)((_, synth) => synth.synthesizeProof(concl))
      case ImplE(impl, hyp)                => Raw("implE")(synthesizeProof(impl))((Raw("_") `.` "by")(synthesizeProof(hyp)))
      case AndI(proofs)                    => Raw("andI")(proofs map synthesizeProof)
      case AndE(cunj, parts, body)         => synthesizeAndE(cunj, parts, body)
      case OrI(alternatives, thm)          => Raw("orI")(alternatives map synthesizeExpr)((Raw("_") `.` "by")(synthesizeProof(thm)))
      case OrE(disj, concl, id, cases)     => ???
      case Prove(expr, hyps)               => Raw("prove")(synthesizeExpr(expr) +: (hyps map synthesizeProof))

      case Let(named, id, body) => updatedVarThen(Var(id), BasicNamer(id)) { (name, synth) =>
        Block(Seq(ValDef(name, synthesizeProof(named)), synth.synthesizeProof(body)))
      }

      case Axiom(notfound) => throw new SynthesisError(s"Could not find reference to theorem $notfound")

      case _: Var          => throw new SynthesisError(s"Cannot synthesize proof term ${proof} (${proof.getClass})")
    }

    def synthesizeTopLevel(expr: Expr, sugg: TopLevelSuggestion): ScalaAST = {
      sugg match {
        case NegateTwice => expr match {
          case Not(Not(body)) => Raw("notE")(suggest(body))
        }

        case SplitCases => expr match {
          case And(exprs) =>
            val parts = exprs.zipWithIndex map {
              case (e, i) => ValDef(chooseName(BasicNamer(s"part${i + 1}")), suggest(e))
            }
            Block(parts :+ Raw("andI")(parts.map { case ValDef(ValDecl(name, _), _) => Raw(name) }))
        }

        case FixVariable => expr match {
          case Forall(Seq(vd), body)  => synthesizeForallI(vd)(_.suggest(body))
          case Forall(vd +: vs, body) => synthesizeForallI(vd)(_.suggest(Forall(vs, body)))
        }

        case StructuralInduction =>
          val (v, body) = expr match {
            case Forall(Seq(v), body)  => (v, body)
            case Forall(v +: vs, body) => (v, Forall(vs, body))
          }

          val prop = updatedVarThen(v, BasicNamer(v.id.name)) { (name, synth) =>
            Function(Seq(ValDecl(name, Some(Raw("Expr")))), synth.synthesizeExpr(body))
          }

          updatedVarsThen(Seq(((), BasicNamer("ihs")), ((), BasicNamer("goal")))) { (names, synth) =>
            val cases = ADTDeconstructable.cases(v.tpe.asInstanceOf[ADTType]) map {
              case (Reflected(constrId), expr, vars) => synth.updatedVarsThen(vars map (v => (v, BasicNamer(v.id.name)))) { (names, synth) =>
                val (constrPat, guard) = constrId match {
                  case Raw(id) => (BackTicks(id), None)
                  case _       => (ValDecl("constr", None), Some((Raw("constr") `.` "==")(constrId)))
                }

                Case(Unapply(Raw("C"), constrPat +: (names: Seq[Pattern])), guard,
                  synth.suggest(exprOps.replaceFromSymbols(Map(v -> expr), body)))
              }
            }

            Raw("structuralInduction")(prop, synthesizeValDef(v))(
              PartialFunction(Seq(Case(Unapply(Raw(""), names), None, Match(Raw(names.head) `.` "expression", cases)))))
          }

        case AssumeHypothesis(false) => expr match {
          case Implies(hyp, body) => synthesizeImplI("thm", hyp)((_, synth) => synth.suggest(body))
        }

        case AssumeHypothesis(true) => expr match {
          case Implies(hyp @ And(parts), body) => synthesizeImplI("thm", hyp) { (name, synth) =>
            updatedVarsThen(parts.map(e => ((), ExprNamer(BasicNamer("part"))(e)))) { (vars, rec) =>
              Block(Seq(ValDef(Unapply(Raw("Seq"), vars), Ascript(Raw("andE")(Raw(name)), Raw("Seq[Theorem]"))),
                synth.suggest(body)))
            }
          }
        }

        case ToChain => expr match {
          case Equals(lhs, rhs) => ((synthesizeExpr(lhs) `.` Rel.EQ)(inlineSuggest) `.` Rel.CONCAT)(synthesizeExpr(rhs))
        }
      }
    }

    def synthesizeInner(side: Expr, otherSide: Expr, sugg: InnerSuggestion): (ScalaAST, ScalaAST, ScalaAST) = {
      sugg match {
        case RewriteSuggestion(_, res, proof) =>
          val synthedProof = proof.proof match {
            case Prove(Equals(`side`, `res`), Seq()) => Raw("trivial")
            case other                               => synthesizeProof(other)
          }

          val nextProof = prove(Equals(res, otherSide)) match {
            case Success(_) => Raw("trivial")
            case _          => inlineSuggest
          }

          (synthesizeExpr(res), synthedProof, nextProof)
      }
    }
  }

  def synthesizeTopLevel(expr: Expr, sugg: TopLevelSuggestion)(ctx: ReflectedContext): ScalaAST =
    Synthesizer(ctx).synthesizeTopLevel(expr, sugg)

  def synthesizeInner(side: Expr, otherSide: Expr, sugg: InnerSuggestion)(ctx: ReflectedContext): (ScalaAST, ScalaAST, ScalaAST) =
    Synthesizer(ctx).synthesizeInner(side, otherSide, sugg)
}