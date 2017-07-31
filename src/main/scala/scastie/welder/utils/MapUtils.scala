package scastie.welder.utils

object MapUtils {
  implicit class MapHelpers[K, V](val m: Map[K, V]) extends AnyVal {
    def adjusted(key: K, default: => V)(f: V => V): Map[K, V] = m.updated(key, f(m.getOrElse(key, default)))
  }
}