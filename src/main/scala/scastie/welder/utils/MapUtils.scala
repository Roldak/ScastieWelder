package scastie.welder.utils

import scala.collection.mutable.{Map => MutableMap}

object MapUtils {
  implicit class MapHelpers[K, V](val m: Map[K, V]) extends AnyVal {
    def adjusted(key: K, default: => V)(f: V => V): Map[K, V] = m.updated(key, f(m.getOrElse(key, default)))
  }
  
  implicit class MutableMapHelpers[K, V](val m: MutableMap[K, V]) extends AnyVal {
    def adjust(key: K, default: => V)(f: V => V): Unit = m.update(key, f(m.getOrElse(key, default)))
  }
}