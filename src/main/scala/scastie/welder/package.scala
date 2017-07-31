package scastie

import scastie.welder.macros._

import _root_.welder._
import inox._
import inox.trees._

package object welder {
  trait AssistedTheory extends Theory with Deconstructions with Proofs {
    import scala.language.experimental.macros
    
    def suggest(expr: Expr): Attempt[Theorem] = macro Macros.suggest
    def suggest: Attempt[Theorem] = macro Macros.suggestInline
  }

  def assistedTheoryOf(prgm: InoxProgram): AssistedTheory = new AssistedTheory {
    override val program = prgm
  }
}