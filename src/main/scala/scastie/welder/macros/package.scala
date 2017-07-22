package scastie.welder

package object macros {
  import scala.language.experimental.macros

  def suggest(e: String): Unit = macro Macros.suggest
}