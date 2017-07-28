package scastie.welder

import macros._

import welder._
import inox._
import inox.trees._

trait Interface {
  val theory: NTheory

  import scala.language.experimental.macros
  import theory._

  def suggest(expr: Expr): Attempt[Theorem] = macro Macros.suggest
}