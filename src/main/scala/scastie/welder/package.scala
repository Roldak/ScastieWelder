package scastie

import scastie.welder.macros._

import _root_.welder._
import inox._
import inox.trees._

package object welder {
  trait AssistedTheory extends Theory with Proofs {
    import scala.language.experimental.macros
    def suggest(expr: Expr): Attempt[Theorem] = macro Macros.suggest
  }

  def assistedTheoryOf(prgm: InoxProgram): AssistedTheory = new AssistedTheory {
    override val program = prgm
  }
}