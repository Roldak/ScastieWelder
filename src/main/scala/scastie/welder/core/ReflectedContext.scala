package scastie.welder.core

import scastie.welder.utils.MapUtils._

class ReflectedContext(private val values: Map[String, Any]) {
  private val inversedValues = values.foldLeft(Map.empty[Any, String]) {
    case (acc, (name, value)) => acc.adjusted(value, null) {
      case str if str != null => if (str.size > name.size) name else str
      case _ => name
    }
  }
  
  def get(value: Any): Option[String] = inversedValues.get(value)
  def get(value: Any)(orElse: => String): String = inversedValues.getOrElse(value, orElse)
  
  def existsPath(path: String): Boolean = values.isDefinedAt(path)
  
  def collect[T](pf: PartialFunction[(String, Any), T]): Iterable[T] = values.collect(pf) 
}