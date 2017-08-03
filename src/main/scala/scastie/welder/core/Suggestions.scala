package scastie.welder.core

import welder._
import inox._
import inox.trees._

trait Suggestions { self: Assistant =>
  import theory._
  
  protected[core] sealed abstract class Suggestion
  protected[core] sealed abstract class TopLevelSuggestion extends Suggestion
  protected[core] sealed abstract class InnerSuggestion extends Suggestion
  
  protected[core] case class RewriteSuggestion(subject: Expr, rootRes: Expr, proof: Result) extends InnerSuggestion
  protected[core] case object NegateTwice extends TopLevelSuggestion 
  protected[core] case object SplitCases extends TopLevelSuggestion 
  protected[core] case object FixVariable extends TopLevelSuggestion 
  protected[core] case object StructuralInduction extends TopLevelSuggestion 
  protected[core] case object AssumeHypothesis extends TopLevelSuggestion 
  protected[core] case object ToChain extends TopLevelSuggestion 
  
  protected[core] type NamedTopLevelSuggestion = (String, TopLevelSuggestion)
  protected[core] type NamedInnerSuggestion = (String, InnerSuggestion)
}