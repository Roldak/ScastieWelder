package scastie.welder.utils

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._
import scastie.welder._
import scastie.welder.core.Assistant

trait ExprOps { self: Assistant =>
  import self.theory._
  
  /*
   * Unifies the two patterns, where instantiableVars denotes the set of variables appearing in any of the two patterns that are instantiable.
   */
  def unify(p1: Expr, p2: Expr, instantiableVars: Set[Variable]): Option[Substitution] = (p1, p2) match {
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
}