package scastie

import _root_.welder._

package object welder {
  def interfaceOf(thry: Theory): Interface { val theory: thry.type } = new Interface {
    override val theory: thry.type = thry
  }
}