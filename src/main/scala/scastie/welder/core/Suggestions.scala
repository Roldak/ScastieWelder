package scastie.welder.core

import welder._
import inox._
import inox.trees._

trait Suggestions { self: Assistant =>
  import theory._
  
  protected[core] sealed abstract class Suggestion
  protected[core] case class RewriteSuggestion(subject: Expr, rootRes: Expr, proof: Result) extends Suggestion
  protected[core] case object NegateTwice extends Suggestion
  protected[core] case object SplitCases extends Suggestion
  protected[core] case object FixVariable extends Suggestion
  protected[core] case object StructuralInduction extends Suggestion
  protected[core] case object AssumeHypothesis extends Suggestion
  
  protected[core] type NamedSuggestion = (String, Suggestion)
}