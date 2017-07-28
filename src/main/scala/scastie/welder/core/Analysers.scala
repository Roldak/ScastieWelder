package scastie.welder.core

import welder._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._
import inox.ast.TreeDeconstructor
import inox.ast.TreeExtractor
import inox.evaluators.EvaluationResults._
import scastie.welder.utils._

private object Utils {
  implicit class BoolToOption(val self: Boolean) extends AnyVal {
    def toOption[A](value: => A): Option[A] = if (self) Some(value) else None
  }

  def asADTType(tpe: Type): Option[ADTType] = tpe match {
    case t: ADTType => Some(t)
    case _          => None
  }
}

protected[core] trait Analysers extends PathTreeOps { self: Assistant =>
  import theory._

  private object Rules {

    // introduction rules
    def forallI(vs: Seq[ValDef])(f: Seq[Variable] => Attempt[Result]): Attempt[Result] =
      f(vs map (_.toVariable)) flatMap { res =>
        vs.foldRight(res) {
          case (x, Result(proof, expr)) => Result(ForallI(x, proof), Forall(Seq(x), expr))
        }
      }

    def andI(ps: Seq[Result]): Result =
      Result(AndI(ps map (_.proof)), And(ps map (_.expression)))

    def implI(name: String, prem: Expr)(concl: (String, Result) => Attempt[Result]): Attempt[Result] =
      concl(name, Result(Var(name), prem)) flatMap {
        case Result(proof, expr) => Result(ImplI(name, prem, proof), Implies(prem, expr))
      }

    // elimination rules
    def forallE(forall: Result, exprs: Seq[Expr]): Attempt[Result] =
      forall.expression match {
        case Forall(params, e) if exprs.size == params.size =>
          val proof = exprs.foldLeft(forall.proof)(ForallE(_, _))
          Result(proof, replaceFromSymbols((params zip exprs).toMap, e))
      }

    def andE(and: Result, ids: Seq[String])(f: Seq[(String, Result)] => Attempt[Result]): Attempt[Result] =
      and.expression match {
        case And(exprs) if ids.size == exprs.size =>
          f((ids zip exprs) map { case (id, e) => (id, Result(Var(id), e)) }) flatMap {
            case Result(proof, expr) => Result(AndE(and.proof, ids, proof), expr)
          }
      }

    def andESelect(and: Result, i: Int)(body: Result => Attempt[Result]): Attempt[Result] =
      and.expression match {
        case And(exprs) if exprs.size > i =>
          andE(and, exprs.zipWithIndex map {
            case (e, idx) => if (idx == i) s"tmp$i" else "_"
          }) { parts => body(parts(i)._2) }
      }

    def implE(implication: Result, justification: Result): Attempt[Result] = implication.expression match {
      case Implies(prem, concl) => Result(ImplE(implication.proof, justification.proof), concl)
    }

    def prove(expr: Expr, facts: Seq[Result] = Seq()): Attempt[Result] = Result(Prove(expr, facts map (_.proof)), expr)
  }

  private implicit class IHUtils(hyp: StructuralInductionHypothesis) {
    lazy val variablesSet = hyp.vars.toSet

    private def isInnerOrSelf(inner: Expr): Boolean = inner == hyp.expr || isInner(inner)

    def isInner(inner: Expr): Boolean = inner match {
      case v: Variable           => variablesSet.contains(v)
      case ADTSelector(adt, _)   => isInnerOrSelf(adt)
      case TupleSelect(tuple, _) => isInnerOrSelf(tuple)
      case MapApply(map, _)      => isInnerOrSelf(map)
      case _                     => false
    }
  }

  private type Substitution = Map[Variable, Expr]

  /*
   * Represents a chain of elimination rules
   */
  private sealed abstract class Path
  private case class PNotE(next: Path) extends Path
  private case class PAndE(clauseIndex: Int, next: Path) extends Path
  private case class PForallE(vals: Seq[ValDef], next: Path) extends Path
  private case class PImplE(assumption: Expr, next: Path) extends Path
  private case object PEndOfPath extends Path

  /*
   * Represents one conclusion of a theorem.
   * See "conclusionsOf" for details.
   */
  private case class Conclusion(expr: Expr, freeVars: Set[Variable], premises: Seq[Expr], path: Path) {
    def notE = Conclusion(expr, freeVars, premises, PNotE(path))
    def andE(index: Int) = Conclusion(expr, freeVars, premises, PAndE(index, path))
    def forallE(vals: Seq[ValDef]) = {
      val freshVals = vals map (_.freshen)
      val freshVars = freshVals map (_.toVariable)
      val subst = vals.map(_.toVariable).zip(freshVars).toMap
      Conclusion(replaceFromSymbols(subst, expr), freeVars ++ freshVars, premises map (replaceFromSymbols(subst, _)), PForallE(freshVals, path))
    }
    def implE(assumption: Expr) = Conclusion(expr, freeVars, premises :+ assumption, PImplE(assumption, path))
  }

  /*
   * Generates all the conclusions of an expression (normally, the expression of a theorem)
   * Basically conclusions of a given theorem are all the theorems that you could possibly generate from the
   * initial theorem by applying elimination rules, such as forallE, implE, etc.
   *
   * Example:
   * input:  Vx. Vy. f(x) => (g(y) && Vz. h(z))
   * output: [
   * 	Vx. Vy. f(x) => (g(y) && Vz. h(z)) 		(no rules applied)
   *  Vy. f(x) => (g(y) && Vz. h(z)) 				(forallE(x))
   *  f(x) => (g(y) && Vz. h(z)) 						(forallE(x), forallE(y))
   *  g(y) && Vz. h(z) 											(forallE(x), forallE(y), implE(f(x)))
   *  g(y) 																	(forallE(x), forallE(y), implE(f(x)), andE(0))
   *  Vz. h(z) 															(forallE(x), forallE(y), implE(f(x)), andE(1))
   *  h(z)																	(forallE(x), forallE(y), implE(f(x)), andE(1), forallE(z))
   * ]
   */
  private def conclusionsOf(thm: Expr): Seq[Conclusion] = {
    val paths = thm match {
      case Not(Not(e)) =>
        conclusionsOf(e) map (_.notE)

      case And(exprs) =>
        exprs.zipWithIndex flatMap { case (e, i) => conclusionsOf(e) map (_.andE(i)) }

      case Forall(vals, body) =>
        conclusionsOf(body) map (_.forallE(vals))

      case Implies(assumption, rhs) =>
        conclusionsOf(rhs) map (_.implE(assumption))

      case _ => Nil
    }

    paths :+ Conclusion(thm, Set.empty, Nil, PEndOfPath)
  }

  var analysisTimer: Long = 0
  private def time[T](f: => T): T = {
    val t0 = System.nanoTime()
    val res = f
    analysisTimer += System.nanoTime() - t0
    res
  }

  /*
   * Unifies the two patterns, where instantiableVars denotes the set of variables appearing in any of the two patterns that are instantiable.
   */
  private def unify(p1: Expr, p2: Expr, instantiableVars: Set[Variable]): Option[Substitution] = (p1, p2) match {
    case (v1: Variable, v2: Variable) if v1 == v2 =>
      if (instantiableVars(v1)) None
      else Some(Map.empty)

    case (v1: Variable, v2: Variable) if instantiableVars(v1) =>
      if (instantiableVars(v2)) None
      else if (v1.tpe == v2.tpe) Some(Map(v1 -> v2))
      else None

    case (v1: Variable, v2: Variable) if instantiableVars(v2) =>
      if (instantiableVars(v1)) None
      else if (v2.tpe == v1.tpe) Some(Map(v2 -> v1))
      else None

    case (expr, pv: Variable) =>
      if (instantiableVars(pv) && expr.getType == pv.tpe) Some(Map(pv -> expr))
      else None

    case (pv: Variable, expr) =>
      if (instantiableVars(pv) && expr.getType == pv.tpe) Some(Map(pv -> expr))
      else None

    case (p1, p2) if p1.getClass == p2.getClass =>
      val (vars1, exprs1, types1, builder1) = deconstructor.deconstruct(p1)
      val (vars2, exprs2, types2, builder2) = deconstructor.deconstruct(p2)

      if (vars1.size == vars2.size &&
        exprs1.size == exprs2.size &&
        types1 == types2 &&
        vars1.map(_.tpe) == vars2.map(_.tpe) &&
        builder2(vars1, exprs1, types1) == p1) {

        val subExprs2 = exprs2 map (replaceFromSymbols(vars2.zip(vars1).toMap, _))

        // Creates the substitution by recursively unifying both patterns' subexpressions together.
        // At each iteration of the foldLeft:
        //  - The substitution becomes (equal or) bigger, or None to indicate that the sub-unification has failed. 
        //     (The failure is then propagated to the base unification.)
        //  - The instantiableVars become (equal or) smaller, because some of them have been successfully unified with some expression.
        exprs1.zip(subExprs2).foldLeft[(Option[Substitution], Set[Variable])]((Some(Map.empty), instantiableVars)) {
          case ((Some(subst), instantiable), (sp1, sp2)) =>
            unify(replaceFromSymbols(subst, sp1), replaceFromSymbols(subst, sp2), instantiable) match {
              case Some(stepSubst) => (Some(subst ++ stepSubst), instantiable -- stepSubst.keys)
              case _               => (None, instantiable)
            }
          case (none, _) => none
        }._1
      } else
        None
    case _ => None
  }

  import scala.language.implicitConversions

  private implicit def attemptToOption[T](x: Attempt[T]): Option[T] = x match {
    case Success(v) => Some(v)
    case _          => None
  }

  private object TheoremWithExpression {
    def unapply(thm: Result): Option[(Result, Expr)] = Some((thm, thm.expression))
  }

  /*
   * Generates a new theorem from a given theorem by following elimination rules given by the path,
   * with the help of a substitution to instantiate foralls and of proofs to instantiate the premises.
   * implE(thm)(goal => {println(s"${goal.expression} VS ${instPrems.head.expression}"); time(goal.by(instPrems.head))})
   */
  private def followPath(thm: Result, path: Path, subst: Substitution, instPrems: Seq[Result]): Result = path match {
    //case NotE(next)              => followPath(notE(thm), next, subst, instPrems)
    case PAndE(i, next)           => Rules.andESelect(thm, i) (followPath(_, next, subst, instPrems))
    case PForallE(vals, next)     => followPath(Rules.forallE(thm, vals map (_.toVariable) map subst), next, subst, instPrems)
    case PImplE(assumption, next) => followPath(Rules.implE(thm, instPrems.head), next, subst, instPrems.tail)
    case PEndOfPath               => thm
  }

  /*
   * Homemade "prove" that returns the proof of the given theorem possibly containing variables to instantiate 
   * together with the instantiation of such variables. Needs the list of all available theorems (avThms).
   *  
   * Note that "instantiableVars" are actually required to be instantiated. This means that every (and only) instantiableVars 
   * are valid keys in the substitution returned.
   *  
   * The main mechanism for finding the proofs (and the substitutions) is unification.
   */

  private def provePattern(expr: Expr, instantiableVars: Set[Variable], avThms: Seq[Result]): Seq[(Substitution, Result)] = {
    val deeps = expr match {
      case And(exprs) =>
        proveDependentSequence(exprs, instantiableVars, Map.empty, avThms) map (s => (s._1, Rules.andI(s._2)))

      case Forall(vals, body) =>
        provePattern(body, instantiableVars, avThms) flatMap (s => Rules.forallI(vals)(_ => s._2) map (thm => Seq((s._1, thm))) getOrElse (Nil))

      // TODO: support more cases

      case _ => Nil
    }

    deeps ++ avThms.foldLeft[Seq[(Substitution, Result)]](Nil) { (acc, thm) =>
      acc ++ (conclusionsOf(thm.expression) flatMap {
        case Conclusion(pattern, freeVars, premises, path) =>
          instantiatePath(expr, pattern, path, freeVars ++ instantiableVars, premises, avThms) flatMap {
            case (subst, prems) if freeVars forall (subst isDefinedAt _) => Seq((subst, followPath(thm, path, subst, prems)))
            case _ => Nil
          }
      })
    }
  }

  /*
   * Proves a sequence of pattern expressions (using provePattern) sharing the same set of instantiable vars.
   */
  private def proveDependentSequence(exprs: Seq[Expr], instantiable: Set[Variable], sub: Substitution,
                                     avThms: Seq[Result], provedExprs: Seq[Result] = Nil): Seq[(Substitution, Seq[Result])] = exprs match {
    case e +: es =>
      provePattern(replaceFromSymbols(sub, e), instantiable, avThms) flatMap {
        case (thisSub, thm) =>
          proveDependentSequence(es, instantiable -- thisSub.keys, sub ++ thisSub, avThms, provedExprs :+ thm)
      }
    case _ => Seq((sub, provedExprs))
  }

  /*
   * Free variables are generally all instantiated by unifying the pattern of the conclusion with the subject expression.
   * However, sometimes this is not enough, as some quantified variables can not appear in the pattern:
   *  - If doesn't appear at all in the formula, then instantiate it with any value
   *  		=> CURRENTLY A LIMITATION (need to conceive a recursive algorithm to generate value of any type I guess, but no time)
   *
   *  - If it appears in a premise of an implication, try to find it with unification
   */
  private def instantiatePath(exp: Expr, pattern: Expr, path: Path, vars: Set[Variable], premises: Seq[Expr], avThms: Seq[Result]): Seq[(Substitution, Seq[Result])] = {
    unify(exp, pattern, vars) match {
      case Some(subst) => proveDependentSequence(premises, vars filterNot (subst isDefinedAt _), subst, avThms)
      case _           => Nil
    }
  }

  /*
   * Given a root expression expr and a root theorem thm,
   * tries to find subexpressions inside expr where some conclusion of thm could be applied.
   */
  private def instantiateConclusion(expr: Expr, thm: Result, avThms: Seq[Result]): Seq[(Expr, Expr, Result)] = {
    val concls = conclusionsOf(thm.expression) flatMap {
      case concl @ Conclusion(Equals(a, b), vars, premises, path) => Seq(
        (a, (x: Equals) => x.lhs, (x: Equals) => x.rhs, vars, premises, path),
        (b, (x: Equals) => x.rhs, (x: Equals) => x.lhs, vars, premises, path))
      case _ => Nil
    }

    collectPreorderWithPath { (exp, exPath) =>
      concls flatMap {
        case (pattern, from, to, freeVars, premises, path) =>
          instantiatePath(exp, pattern, path, freeVars, premises, avThms) flatMap {
            case (subst, prems) if freeVars forall (subst isDefinedAt _) => followPath(thm, path, subst, prems) match {
              case TheoremWithExpression(thm, eq: Equals) => Seq((from(eq), replaceTreeWithPath(expr, exPath, to(eq)), thm))
            }
            case _ => Nil
          }
      }
    }(expr).groupBy(x => (x._1, x._2)).map(_._2.head).toSeq
  }

  /*
   * Given a root expression expr and a collection of theorems thms,
   * finds all possible applications of any theorem in thms on any subexpression of expr
   */
  private def findTheoremApplications(expr: Expr, thms: Map[String, Result]): Seq[NamedSuggestion] = {
    thms.toSeq flatMap {
      case (name, thm) =>
        instantiateConclusion(expr, thm, thms.values.toSeq) map {
          case (subj, res, proof) => (s"Apply theorem $name", RewriteSuggestion(subj, res, proof))
        }
    }
  }

  /*
   * Collect function calls in the expression and generates suggestion for expanding them (using partial evaluation)
   */
  private def collectInvocations(e: Expr): Seq[NamedSuggestion] = functionCallsOf(e).flatMap { inv =>
    PartialEvaluator.default(program, Some(inv)).eval(e) match {
      case Successful(ev) => Seq((s"Expand invocation of '${inv.id}'", RewriteSuggestion(inv, ev, Rules.prove(e === ev))))
      case _              => Nil
    }
  }.toSeq

  /*
   * Finds expressions which can be applied to the inductive hypothesis in order to generate a new theorem.
   */
  private def findInductiveHypothesisApplication(e: Expr, ihses: Map[String, StructuralInductionHypothesis]): Map[String, Result] = {
    val ihset = ihses.toSet
    val thms = collect[(String, Result)] { e: Expr =>
      ihset.flatMap {
        case (id, ihs) =>
          if (ihs.isInner(e)) {
            ihs.hyp(e) match {
              case Success(thm) => Set((s"""IH "$id" on `$e`""", thm))
              case Failure(_)   => Set.empty[(String, Result)]
            }
          } else Set.empty[(String, Result)]
      }
    }(e)

    thms.toMap
  }

  /*
   * Generates all suggestions by analyzing the given root expression and the theorems/IHS that are available.
   */
  protected[core] def analyse(e: Expr, thms: Map[String, Result], ihses: Map[String, StructuralInductionHypothesis]): (Seq[NamedSuggestion], Map[String, Result]) = {
    val findInduct = findInductiveHypothesisApplication(e, ihses)
    val newThms = thms ++ findInduct
    (collectInvocations(e) ++ findTheoremApplications(e, newThms), newThms)
  }

  /*
   * Generates suggestions to eliminate a forall.
   * (Either fix the variable, or if its type is inductive, suggest structural induction)
   */
  protected[core] def analyseForall(v: ValDef, body: Expr): Seq[NamedSuggestion] = {
    import Utils._

    val structInd = asADTType(v.tpe)
      .flatMap(_.lookupADT.flatMap(_.definition.isInductive.toOption(Seq((s"Structural induction on '${v.id}'", StructuralInduction))))) // sorry
      .getOrElse(Nil)

    structInd :+ (s"Fix variable '${v.id}'", FixVariable)
  }
}