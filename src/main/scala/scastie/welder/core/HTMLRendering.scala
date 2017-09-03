package scastie.welder.core

trait HTMLRendering { self: Assistant =>
  import theory.program.trees._

  private var id = 0
  private def freshId = {
    id += 1
    id - 1
  }

  private case class RenderContext(indent: Int, parents: List[Expr], boundVars: Set[ValDef]) {
    def indented = RenderContext(indent + 1, parents, boundVars)
    def withParent(e: Expr) = RenderContext(indent, e :: parents, boundVars)
    def withBoundVars(v: Iterable[ValDef]) = RenderContext(indent, parents, boundVars ++ v)
  }

  private object Code {
    private case class Node(text: String, font: String, color: String, underline: Boolean) {
      def withFont(f: String) = copy(font = f)
      def withColor(c: String) = copy(color = c)
      def withUnderline = copy(underline = true)

      override def toString = {
        val style = s"""
          |color: ${if (color.isEmpty) "default" else color};
          |font: ${if (font.isEmpty) "default" else font};
          |text-decoration: ${if (underline) "underline" else "default"};
          |""".stripMargin.replaceAllLiterally("\n", "")

        s"""<span style="$style">$text</span>"""
      }
    }

    private def rgb(r: Int, g: Int, b: Int): String = s"rgb($r, $g, $b)"
    private def Black = "black"
    private def DarkGray = "darkgray"

    private def ConsolasItalicFont = "italic consolas"
    private def ConsolasBoldFont = "bold consolas"

    private def Raw(text: String)(implicit ctx: RenderContext) = new Node(text, "consolas", "", false)

    implicit def node2string(x: Node): String = x.toString

    def Operator(text: String)(implicit ctx: RenderContext): String = Raw(text) withColor Black
    def TreeName(text: String)(implicit ctx: RenderContext): String = Raw(text) withColor rgb(181, 58, 103)
    def Literal(text: String)(implicit ctx: RenderContext): String = Raw(text) withColor rgb(226, 160, 255)
    def Identifier(text: String)(implicit ctx: RenderContext): String = Raw(text) withColor rgb(94, 94, 255)
    def BoundVar(text: String)(implicit ctx: RenderContext): String = Raw(text) withColor DarkGray withFont ConsolasItalicFont
    def Type(text: String)(implicit ctx: RenderContext): String = Raw(text) withColor Black
    def ADTType(text: String)(implicit ctx: RenderContext): String = Raw(text) withColor rgb(210, 87, 0) withFont ConsolasBoldFont
    def Keyword(text: String)(implicit ctx: RenderContext): String = Raw(text) withColor rgb(193, 58, 85) withFont ConsolasBoldFont
    def Indent(n: Int)(implicit ctx: RenderContext): String = Raw("  " * n)

    def OpeningBracket(implicit ctx: RenderContext) = Operator("(")
    def ClosingBracket(implicit ctx: RenderContext) = Operator(")")
    def OpeningSquareBracket(implicit ctx: RenderContext) = Operator("[")
    def ClosingSquareBracket(implicit ctx: RenderContext) = Operator("]")
    def OpeningBrace(implicit ctx: RenderContext) = Operator("{")
    def ClosingBrace(implicit ctx: RenderContext) = Operator("}")
    def CommaSpace(implicit ctx: RenderContext) = Operator(", ")
    def Dot(implicit ctx: RenderContext) = Operator(".")
    def Colon(implicit ctx: RenderContext) = Operator(":")
    def Space(implicit ctx: RenderContext) = Operator(" ")
    def LineBreak(implicit ctx: RenderContext) = Operator("\n")
  }

  private object BinaryOperator {
    def unapply(e: Expr): Option[(Expr, Expr, String)] = e match {
      case Equals(a, b)  => Some((a, b, "=="))
      case Implies(a, b) => Some((a, b, "==>"))
      case _             => None
    }
  }

  private def renderExpr(expr: Expr): String = {
    import Code._
    
    def nary(exprs: Seq[String], sep: String = ", ", start: String = "", end: String = "", hideIfEmptyExprs: Boolean = false)(implicit ctx: RenderContext): String = {
      val str = exprs mkString sep
      if (hideIfEmptyExprs && str.isEmpty) ""
      else start + str + end
    }

    def rec(expr: Expr)(implicit ctx: RenderContext): String = {
      val res = inner(expr)
      val mouseEvents = """onmouseover="overExpr(event, this)" onmouseout="outExpr(event, this)""""
      s"""<span $mouseEvents id="expr_$freshId">$res</span>"""
    }

    def typeNode(tpe: Type)(implicit ctx: RenderContext): String = Type(prettyPrint(tpe, PrinterOptions()))

    def block(stmt: String)(implicit ctx: RenderContext): String =
      OpeningBrace + LineBreak + Indent(ctx.indent + 1) + stmt + LineBreak + Indent(ctx.indent) + ClosingBrace

    def inner(expr: Expr)(implicit ctx: RenderContext): String = expr match {
      case FractionLiteral(a, b)         => a.toString + "/" + b.toString

      case x: Literal[AnyRef] @unchecked => x.value.toString

      case BinaryOperator(a, b, op)      => rec(a) + s" $op " + rec(b)

      case v @ Variable(id, _, _)        => if (ctx.boundVars contains v.toVal) BoundVar(id.toString) else Identifier(id.toString)

      case FunctionInvocation(f, tps, args) =>
        Identifier(f.toString) + nary(tps map typeNode, ", ", "[", "]", true) + nary(args map rec, ", ", "(", ")")

      case ADT(ADTType(id, tps), args) =>
        ADTType(id.toString) + nary(tps map typeNode, ", ", "[", "]", true) + nary(args map rec, ", ", "(", ")")

      case Application(f, args) =>
        Identifier(f.toString) + nary(args map rec, ", ", "(", ")")

      case ADTSelector(e, id) =>
        rec(e) + Dot + Identifier(id.toString)

      case IsInstanceOf(e, tp) =>
        rec(e) + Dot + Keyword("is") + OpeningSquareBracket + typeNode(tp) + ClosingSquareBracket

      case AsInstanceOf(e, tp) =>
        rec(e) + Dot + Keyword("as") + OpeningSquareBracket + typeNode(tp) + ClosingSquareBracket

      case IfExpr(cond, then, elze) =>
        Keyword("if") + Space + OpeningBracket + rec(cond) + ClosingBracket + Space +
          block(rec(then)(ctx indented)) + Keyword(" else ") + block(rec(elze)(ctx indented))

      case Forall(vals, expr) =>
        Operator("\u2200") + nary(vals.map { v =>
          BoundVar(v.id.toString) + Colon + typeNode(v.tpe)
        }) + Dot + Space + rec(expr)(ctx withBoundVars (vals))

      case And(exprs) =>
        nary(exprs map rec, " && ")

      case Or(exprs) =>
        nary(exprs map rec, " || ")

      case Operator(subexprs, _) => expr.getClass.getSimpleName + nary(subexprs map rec, ", ", "(", ")")
    }

    rec(expr)(RenderContext(0, Nil, Set.empty))
  }

  private val ScriptSetup = """
    |var script = document.createElement('script');
    |var node = this.parentNode.getElementsByTagName('script')[0];
    |script.innerHTML = node.innerHTML;
    |for( var i = node.attributes.length-1; i >= 0; i-- ) {
        |script.setAttribute(node.attributes[i].name, node.attributes[i].value);
    |}
    |""".stripMargin.replaceAllLiterally("\n", "")

  private val JsLoader = s"""<img src="/assets/public/img/icon-scastie.png" onload="$ScriptSetup;this.parentNode.replaceChild(script, this)"/>"""

  def renderHTML(lhs: Expr, rhs: Expr, suggs: Seq[SynthesizedInnerSuggestion], chainStart: Int, chainEnd: Int): String = {
    val js = """<script type="text/javascript">
      function childExprs(node) {
        var nodes = Array.from(node.getElementsByTagName("*"))
        nodes.push(node)
        return nodes.filter(function(n) { return !!n.id && n.id.startsWith("expr_") })
      }
      
      function overExpr(event, node) {
        event.stopPropagation()
        childExprs(node).forEach(function(n) {
          n.style.textDecoration = "underline"
        })
      }
      
      function outExpr(event, node) {
        childExprs(node).forEach(resetStyle)
      }
      
      function resetStyle(exprNode) {
        var style = exprStyles[exprNode.id]
        if (!!style) {
          exprNode.style = style
        }
      }
      
      function registerExprStyles() {
        childExprs(document).forEach(function(n) {
          exprStyles[n.id] = n.style
        })
      }
      
      var exprStyles = {}
      registerExprStyles()
    </script>"""

    val head = renderExpr(lhs) + """<br><br>"""
    suggs.groupBy(_.title).mapValues(_.groupBy(_.subject))

    js + JsLoader + head + suggs.map {
      case SynthesizedInnerSuggestion(name, replacement, subj, res) =>
        "<button onclick='ScastieExports.replaceCode(" + chainStart + ", " + chainEnd + ", \"" + replacement + "\")'>" + name + "</button>" +
          " Preview: " + res.toString + "<br>"
    }.mkString(" ")
  }
}