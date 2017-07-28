package scastie.welder.utils

import inox._
import inox.trees._
import inox.trees.dsl._
import inox.trees.exprOps._
import scastie.welder._
import welder.Theory

trait PathTreeOps {
  val theory: Theory
  
  type TreePath = Seq[Int]
  
  def foldWithPath[T](f: (Source, TreePath, Seq[T]) => T)(e: Source, p: TreePath): T = {
    val Deconstructor(es, _) = e
    f(e, p, es.zipWithIndex.view.map(ei => foldWithPath(f)(ei._1, p :+ ei._2)))
  }
  
  def collectWithPath[T](matcher: (Source, TreePath) => Set[T])(e: Source): Set[T] = {
    foldWithPath[Set[T]]({ (e, path, subs) => matcher(e, path) ++ subs.flatten } )(e, Nil)
  }
  
  def collectPreorderWithPath[T](matcher: (Source, TreePath) => Seq[T])(e: Source): Seq[T] = {
    foldWithPath[Seq[T]]({ (e, path, subs) => matcher(e, path) ++ subs.flatten } )(e, Nil)
  }
  
  def replaceTreeWithPath(expr: Source, path: TreePath, replaceWith: Source): Source = path match {
    case i +: is =>
      val Deconstructor(es, builder) = expr
      builder(es.updated(i, replaceTreeWithPath(es(i), is, replaceWith)))
      
    case _ => replaceWith
  }
}