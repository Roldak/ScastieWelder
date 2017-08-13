package scastie.welder.core

import scastie.welder.utils.MapUtils._

import scastie.welder.codegen.ScalaAST
import scastie.welder.codegen.ScalaAST.{ Raw, PartialFunction => _ }

class ReflectedContext private (private val values: Map[ScalaAST, Any], private val inversedValues: Map[Any, Seq[ScalaAST]]) {
  def this(values: Map[ScalaAST, Any]) = this(values, values.groupBy(_._2).mapValues(_.keys.toSeq))
  
  def get(value: Any): Option[ScalaAST] = inversedValues.get(value).map(ReflectedContext.shortest)
  def existsPath(path: ScalaAST): Boolean = values.isDefinedAt(path)
  def collect[T](pf: PartialFunction[(ScalaAST, Any), T]): Iterable[T] = values.collect(pf)

  def updated(path: ScalaAST, value: Any) = new ReflectedContext(values.updated(path, value), inversedValues.adjusted(value, Nil)(path +: _))
}

object ReflectedContext {
  def apply(values: Map[String, Any]): ReflectedContext = new ReflectedContext(values.map { case (k, v) => (Raw(k): ScalaAST, v) })

  private def shortest(xs: Seq[ScalaAST]): ScalaAST = xs.reduce(shortest)

  private def shortest(a: ScalaAST, b: ScalaAST): ScalaAST = (a, b) match {
    case (Raw(pathA), Raw(pathB)) => if (pathA.size < pathB.size) a else b
    case (a: Raw, _)              => a
    case (_, b: Raw)              => b
    case _                        => a
  }
}