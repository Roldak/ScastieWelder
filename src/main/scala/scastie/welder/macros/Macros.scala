package scastie.welder.macros

import scala.reflect.macros.blackbox.Context
import scastie.welder.core.Assistant
import scastie.welder._

class Macros(val c: Context)
    extends MacroHelpers
    with ContextAnalysis {

  import c.universe._

  assert(c.prefix.actualType <:< c.typeOf[AssistedTheory])

  private def originalPos(pos: Int): Tree = q"""OriginalFile.getOriginalPos($pos)"""

  private val start = originalPos(c.macroApplication.pos.start)
  private val end = originalPos(c.macroApplication.pos.end)

  lazy val rewriteAnnotationType = c.prefix.tree.tpe.member(TypeName("rewrite")).asType.toTypeIn(c.prefix.tree.tpe)
  
  lazy val reflectedContext = {
    val values = reachableDefs.filter(!_.symbol.isMethod).map(vd => vd.name.toString -> vd.name).toMap

    val rewrites = reachableDefs.flatMap(rdef => rdef.symbol.annotations.find(_.tree.tpe =:= rewriteAnnotationType).map(annot => (rdef, annot))).map {
      case (rewrite, annot) =>
        val annotArgs = annot.tree.children.tail
        val (valdefs, vars) = annotArgs.zipWithIndex.map {
          case (p, i) =>
            val name = TermName(s"v$i")
            (q"""val $name = Variable.fresh(${s"v$i"}, $p)""", q"$name")
        } unzip

        val res = q"""{
          ..$valdefs
          new ${c.prefix}.RewriteRule(${rewrite.name.toTermName}(..$vars), Seq(..$vars))
        }"""

        rewrite.name.toString -> res
    }.toMap

    q"scastie.welder.core.ReflectedContext($values ++ $rewrites)"
  }
  
  lazy val expansionInit = q"""
      import com.olegych.scastie.api._
	    val reflCtx = ${reflectedContext}
	    val codeGen = new scastie.welder.codegen.NaiveGenerator
	    val assistant = scastie.welder.core.Assistant(${c.prefix}, codeGen)
    """

  def suggest(expr: Tree): Tree = {
    val call = q"""assistant.suggest(expr)(reflCtx)"""

    q"""
	    {
	      ..$expansionInit
	      
	      val expr = $expr
        val str = "<h1>Select suggestion to apply</h1><br><br>" + $call.map { case assistant.SynthesizedTopLevelSuggestion(name, replacement) =>
          "<button onclick='ScastieExports.replaceCode(" + $start + ", " + $end + ", \"" + replacement + "\")'>" + name + "</button>"
        }.mkString(" ")
	      println(Runtime.write(List(Instrumentation(Position($start, $end), Html(str)))))
	      prove(expr)
	    }
	    """
  }

  private lazy val chainContextInit: Tree = {
    def copyOf(t: Tree): Tree = {
      val start = originalPos(t.pos.start)
      val end = originalPos(t.pos.end)
      q"""Raw("%%%" + $start + "->" + $end + "%%%")"""
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
          q"""(${genChainTree(prev)} `.` Constants.Rel.CONCAT)((res `.` Constants.Rel.EQ)(${proofOrSugg(1 - side)}))"""
        else
          genChainTree(prev)

        q"""($prevAST `.` Constants.Rel.CONCAT)(${genChainTree(next)})"""
    }

    def genChain(chain: OpChain)(implicit side: Int): Tree = {
      val rootAST = if (chain == enclosingOpSegment)
        q"""(${genChainTree(enclosingOpChain.root)} `.` Constants.Rel.CONCAT)((res `.` Constants.Rel.EQ)(${proofOrSugg(1 - side)}))"""
      else
        genChainTree(enclosingOpChain.root)

      q"""($rootAST `.` Constants.Rel.CONCAT)(${copyOf(enclosingOpChain.expr)})"""
    }

    val chainAstLHS: Tree = genChain(enclosingOpChain)(LHS)
    val chainAstRHS: Tree = genChain(enclosingOpChain)(RHS)

    q"""
      import scastie.welder.codegen._
      import scastie.welder.codegen.ScalaAST._
      import scastie.welder.codegen.ScalaAST.Implicits._
      import scastie.welder.Constants
      
      def contextForLHS(res: ScalaAST, proof: ScalaAST, sugg: ScalaAST): ScalaAST = $chainAstLHS
      def contextForRHS(res: ScalaAST, proof: ScalaAST, sugg: ScalaAST): ScalaAST = $chainAstRHS
    """
  }

  def suggestInline: Tree = {
    val OpChainSegment(lhs, op, rhs, proof) = enclosingOpSegment

    val call = q"""assistant.inlineSuggest(lhs, op, rhs)(contextForLHS, contextForRHS)(reflCtx)"""

    val chainStart = originalPos(enclosingOpChain.pos.start)
    val chainEnd = originalPos(enclosingOpChain.pos.end)

    q"""
	    ({
	      ..$expansionInit
	      
	      val (lhs, op, rhs) = ($lhs, $op, $rhs)
	      
	      ..$chainContextInit
	      
        val str = assistant.renderHTML(lhs, rhs, $call, $chainStart, $chainEnd)
        
	      println(Runtime.write(List(Instrumentation(Position($start, $end), Html(str)))))
	      truth
	    })
	    """
  }
}