package scastie.welder.macros

import scala.reflect.macros.blackbox.Context
import scastie.welder.core.Assistant
import scastie.welder._

class Macros(val c: Context)
    extends MacroHelpers
    with ContextAnalysis {

  import c.universe._

  private val preludeOffset = 354 // hardcoded for now

  def suggest(expr: Tree): Tree = {
    assert(c.prefix.actualType <:< c.typeOf[AssistedTheory])

    val start = c.macroApplication.pos.start - preludeOffset
    val end = c.macroApplication.pos.end - preludeOffset

    /*
    val testtree = q"""ListA"""
    val typedtree = c.typecheck(testtree, c.TERMmode)
    println(typedtree.equalsStructure(c.typecheck(typedtree, c.TERMmode)))
		*/
    //println(reachableValOrDefs map (_.symbol.typeSignature))

    //println("PATH: " + (pathToMacro map (_.getClass.getSimpleName)))
    val values = reachableDefs filter (!_.symbol.isMethod) map (vd => vd.name.toString -> vd.name) toMap

    println(values)

    val call = q"""scastie.welder.core.Assistant(${c.prefix}, reflCtx, codeGen).suggest(expr)"""

    q"""
	    {
	      import com.olegych.scastie.api._
	      val reflCtx = scastie.welder.core.ReflectedContext(${values})
	      val codeGen = new scastie.welder.codegen.NaiveGenerator
	      val expr = $expr
        val str = "<h1>Select suggestion to apply</h1>" + $call.map { case scastie.welder.core.SynthesizedSuggestion(name, replacement) =>
          "<button onclick='ScastieExports.replaceCode(" + $start + ", " + $end + ", \"" + replacement + "\")'>" + name + "</button><br>"
        }.mkString("\n")
	      println(Runtime.write(List(Instrumentation(Position($start, $end), Html(str)))))
	      prove(expr)
	    }
	    """
  }

  private lazy val chainContextInit: Tree = {
    def copyOf(t: Tree): Tree = {
      val start = t.pos.start - preludeOffset
      val end = t.pos.end - preludeOffset
      q"""Raw("%%%" + ${start.toString} + "->" + ${end.toString} + "%%%")"""
    }

    val LHS: Int = 0
    val RHS: Int = 1

    def proofOrSugg(side: Int): Tree = if (side == RHS) q"sugg" else q"proof"

    def genChainTree(ctree: OpChainTree)(implicit side: Int): Tree = ctree match {
      case OpChainLeaf(expr, op, proof) =>
        val proofAST = if (proof == enclosingOpSegment.proof) proofOrSugg(side)
        else copyOf(proof)

        q"""(${copyOf(expr)} `.` ${op.toString})($proofAST)"""

      case node @ OpChainNode(prev, next) =>
        val prevAST = if (node == enclosingOpSegment)
          q"""(${genChainTree(prev)} `.` "|")((res `.` "==|")(${proofOrSugg(1 - side)}))"""
        else
          genChainTree(prev)

        q"""($prevAST `.` "|")(${genChainTree(next)})"""
    }

    def genChain(chain: OpChain)(implicit side: Int): Tree = {
      val rootAST = if (chain == enclosingOpSegment)
        q"""(${genChainTree(enclosingOpChain.root)} `.` "|")((res `.` "==|")(${proofOrSugg(1 - side)}))"""
      else
        genChainTree(enclosingOpChain.root)

      q"""($rootAST `.` "|")(${copyOf(enclosingOpChain.expr)})"""
    }

    val chainAstLHS: Tree = genChain(enclosingOpChain)(LHS)
    val chainAstRHS: Tree = genChain(enclosingOpChain)(RHS)

    q"""
      import scastie.welder.codegen._
      import scastie.welder.codegen.ScalaAST._
      import scastie.welder.codegen.ScalaAST.Implicits._
      
      def contextForLHS(res: ScalaAST, proof: ScalaAST, sugg: ScalaAST): ScalaAST = $chainAstLHS
      def contextForRHS(res: ScalaAST, proof: ScalaAST, sugg: ScalaAST): ScalaAST = $chainAstRHS
    """
  }

  def suggestInline: Tree = {
    assert(c.prefix.actualType <:< c.typeOf[AssistedTheory])

    val start = c.macroApplication.pos.start - preludeOffset
    val end = c.macroApplication.pos.end - preludeOffset

    /*
    val testtree = q"""ListA"""
    val typedtree = c.typecheck(testtree, c.TERMmode)
    println(typedtree.equalsStructure(c.typecheck(typedtree, c.TERMmode)))
		*/
    //println(reachableValOrDefs map (_.symbol.typeSignature))

    //println("PATH: " + (pathToMacro map (_.getClass.getSimpleName)))
    val values = reachableDefs filter (!_.symbol.isMethod) map (vd => vd.name.toString -> vd.name) toMap

    println(values)

    val OpChainSegment(lhs, op, rhs, proof) = enclosingOpSegment
    println(s"$enclosingOpChain   =>    Segment($lhs, $op, $proof, $rhs)")

    val call = q"""scastie.welder.core.Assistant(${c.prefix}, reflCtx, codeGen).inlineSuggest(lhs, op, rhs)(contextForLHS, contextForRHS)"""

    val chainStart = enclosingOpChain.pos.start - preludeOffset
    val chainEnd = enclosingOpChain.pos.end - preludeOffset

    q"""
	    ({
	      import com.olegych.scastie.api._  
	      val reflCtx = scastie.welder.core.ReflectedContext(${values})
	      val codeGen = new scastie.welder.codegen.NaiveGenerator
	      val (lhs, op, rhs) = ($lhs, $op, $rhs)
	      
	      ..$chainContextInit
	      
        val str = "<h1>Select suggestion to apply</h1>" + $call.map { case scastie.welder.core.SynthesizedSuggestion(name, replacement) =>
          "<button onclick='ScastieExports.replaceCode(" + $chainStart + ", " + $chainEnd + ", \"" + replacement + "\")'>" + name + "</button><br>"
        }.mkString("\n")
	      println(Runtime.write(List(Instrumentation(Position($start, $end), Html(str)))))
	      truth
	    })
	    """
  }
}