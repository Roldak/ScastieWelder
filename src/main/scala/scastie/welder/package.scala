package scastie

import _root_.welder._

package object welder {
  type NTheory = Theory with Proofs
  
  def interfaceOf(thry: NTheory): Interface { val theory: thry.type } = new Interface {
    override val theory: thry.type = thry
  }
}