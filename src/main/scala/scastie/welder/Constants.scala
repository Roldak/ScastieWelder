package scastie.welder

object Constants {
  object Rel {
    val LE = "<=%%%LALIGN%%%|"
    val LT = "<<%%%LALIGN%%%|"
    val EQ = "==%%%LALIGN%%%|"
    val GT = ">>%%%LALIGN%%%|"
    val GE = ">=%%%LALIGN%%%|"
    val CONCAT = "%%%RALIGN%%%|"
  }

  protected[welder] val alignPattern = "%%%[LR]ALIGN%%%".r

  protected[welder] case class CleanString protected[Constants] (str: String)

  protected[welder] object Clean {
    private val toCleanOf = List(alignPattern)

    def apply(s: String): CleanString = CleanString(toCleanOf.foldLeft(s) {
      case (str, pat) => pat.replaceAllIn(str, "")
    })

    def unapply(s: CleanString): Option[String] = Some(s.str)
  }

  protected[welder] object Implicits {
    implicit def string2CleanString(x: String): CleanString = Clean(x)
  }
}