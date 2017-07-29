package scastie

import _root_.welder._
import inox._

package object welder {
  type NTheory = Theory with Proofs
  
  def theoryWithProofsOf(prgm: InoxProgram): NTheory = new Theory with Proofs {
    override val program = prgm
  }
  
  def interfaceOf(thry: NTheory): Interface { val theory: thry.type } = new Interface {
    override val theory: thry.type = thry
  }
}