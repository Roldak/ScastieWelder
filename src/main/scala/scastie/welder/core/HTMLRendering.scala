package scastie.welder.core

import scala.collection.mutable.{ Map => MutableMap }

import scastie.welder.utils.MapUtils._

trait HTMLRendering { self: Assistant =>
  import theory.program.trees._

  private var id = 0
  private def freshId = {
    id += 1
    id - 1
  }

  private val exprIdMap = MutableMap[Expr, List[String]]()

  private case class RenderContext(indent: Int, parents: List[Expr], boundVars: Set[ValDef], idChar: Char) {
    def indented = copy(indent = indent + 1)
    def withParent(e: Expr) = copy(parents = e :: parents)
    def withBoundVars(v: Iterable[ValDef]) = copy(boundVars = boundVars ++ v)
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

  private def renderExpr(expr: Expr, idChar: Char): String = {
    import Code._

    def nary(exprs: Seq[String], sep: String = ", ", start: String = "", end: String = "", hideIfEmptyExprs: Boolean = false)(implicit ctx: RenderContext): String = {
      val str = exprs mkString sep
      if (hideIfEmptyExprs && str.isEmpty) ""
      else start + str + end
    }

    def rec(expr: Expr)(implicit ctx: RenderContext): String = {
      val res = inner(expr)
      val id = s"expr_${freshId}_${ctx.idChar}"
      exprIdMap.adjust(expr, Nil)(id :: _)
      s"""<span id="$id">$res</span>"""
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

    rec(expr)(RenderContext(0, Nil, Set.empty, idChar))
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
    val titleMap = suggs.groupBy(_.title).map(_._1).zipWithIndex.toMap

    val top = renderExpr(lhs, 'l') + "\n\n"
    val bot = renderExpr(rhs, 'r')
    val middle = suggs.groupBy(_.title).map {
      case (title, _) => s"""<button onclick="installMode(new SelectSubjectMode(suggestions[${titleMap(title)}]))">$title</button>"""
    } mkString ("", " ", "\n\n")

    val jsSuggestions = suggs.groupBy(_.title).mapValues(_.groupBy(_.subject)).map {
      case (title, next) =>
        val elements = next.filter(x => exprIdMap.contains(x._1)).toSeq.map {
          case (k, v) =>
            val subjectIds = exprIdMap(k).map("\"" + _ + "\"").mkString("[", ", ", "]")
            val suggestions = v.map {
              case SynthesizedInnerSuggestion(_, code, _, resultExpr, isLHS) => s"""{
              |  res: "${escapeProperly(renderExpr(resultExpr, 'n'))}",
              |  lhs: $isLHS
              |}""".stripMargin
            }.mkString("[", ", ", "]")

            s"""{
            |  subjectIds: $subjectIds,
            |  suggestions: $suggestions
            |}""".stripMargin
        }.mkString("[", ", ", "]")

        s"""${titleMap(title)}: $elements"""
    } mkString ("{", ", ", "}")

    val js = s"""<script type="text/javascript">
      function Expr(main, components) {
        this.main = main;
        this.id = main.id;
        this.nodes = components;
        this.isLHS = this.id.endsWith('l');
        
        this.nodes.forEach(function(n){
          n["initStyle"] = n.style.cssText;
          n["styleStack"] = [];
        });
        
        this.pushStyle = function(id, styleSetter) {
          this.nodes.forEach(function(n) {
            if (n.styleStack.length == 0 || n.styleStack[n.styleStack.length - 1].id !== id) {
              n.styleStack.push({id: id, css: n.style.cssText});
              styleSetter(n.style);
            }
          });
        };
        
        this.popStyle = function() {
          this.nodes.forEach(function(n) {
            if (n.styleStack.length > 0) {
              n.style.cssText = n.styleStack.pop().css;
            }
          });
        };
        
        this.resetStyle = function() {
          this.nodes.forEach(function(n) {
            n.style.cssText = n.initStyle;
            n.styleStack = [];
          });
        };
      }
      
      function IdleMode() {
        this.install = resetAllExprsStyle;
        this.uninstall = resetAllExprsStyle;
        
        this.overExpr = function(expr) {
          expr.pushStyle('idleover', function(style) {
            style.textDecoration = "underline";
          });
        };
        
        this.outExpr = function(expr) {
          expr.popStyle();
        };
        
        this.clickExpr = function(expr) {};
      }
      
      function SelectSubjectMode(elements) {
        this.elements = elements;

        var sidedSuggCount = function(elem) {
          return elem.suggestions
            .split(function(sugg) {return sugg.lhs;})
            .map(function(side) {return side.length;})
            .reduce(function(a, b) {return Math.max(a, b)});
        };
        
        var maxSuggsCount = sidedSuggCount(this.elements.reduce(function(a, b) {
          return sidedSuggCount(a) > sidedSuggCount(b) ? a : b; 
        }));
        
        var insertionBlanks = ScastieExports.indentAccordingToPosition($chainStart, "\\n".repeat(maxSuggsCount + 1));
        
        this.showPreviews = function(isLHS, suggestions) {
          var html = suggestions.filter(function(sugg) {
            return sugg.lhs === isLHS;
          }).map(function(sugg, idx) {
            return "<span style='color=lightgray'>" + (idx + 1) + ".</span> " + sugg.res;
          }).resize(maxSuggsCount, "").join("\\n");
          
          var id = isLHS ? 'insert_lhs' : 'insert_rhs';
          
          document.getElementById(id).innerHTML = ScastieExports.indentAccordingToPosition($chainStart, html + "\\n\\n");
        }
        
        this.reInitPreviews = function() {
          document.getElementById("insert_lhs").innerHTML = insertionBlanks;
          document.getElementById("insert_rhs").innerHTML = insertionBlanks;
        }
        
        this.suggestionsFor = function(expr) {
          return this.elements.find(function(elem) {
            return elem.subjectIds.indexOf(expr.id) !== -1;
          }).suggestions;
        };
        
        this.install = function() {
          var subjectIds = Array.prototype.concat.apply([], this.elements.map(function(elem) {
            return elem.subjectIds;
          }));
        
          [this.focused, this.unfocused] = allExprs.split(function(expr) {
            return subjectIds.indexOf(expr.id) !== -1;
          });
          
          this.unfocused.forEach(function(expr) {
            expr.pushStyle('unfocused', function(style) {
              style.color = "darkgray";
            });
          });
          
          this.reInitPreviews();
        };
        
        this.uninstall = function() {
          resetAllExprsStyle();
          document.getElementById("insert_lhs").innerHTML = "";
          document.getElementById("insert_rhs").innerHTML = "";
        }
        
        this.overExpr = function(expr) {
          if (this.focused.indexOf(expr) !== -1) {
            expr.pushStyle('subjectover', function(style) {
              style.textDecoration = "underline";
              style.cursor = "pointer";
            });
            
            this.showPreviews(expr.isLHS, this.suggestionsFor(expr));
          }
        };
        
        this.outExpr = function(expr) {
          if (this.focused.indexOf(expr) !== -1) {
            expr.popStyle();
            this.reInitPreviews();
          }
        };
        
        this.clickExpr = function(expr) {
          if (this.focused.indexOf(expr) !== -1) {
            installMode(new IdleMode());
            
            console.log(this.suggestionsFor(expr));
          }
        };
      }
      
      function overExpr(event, expr) {
        event.stopPropagation();
        if (!similarEvents(lastEvent, event)) {
          lastEvent = event;
          currentMode.overExpr(expr);
        }
      }
      
      function outExpr(event, expr) {
        event.stopPropagation();
        if (!similarEvents(lastEvent, event)) {
          lastEvent = event;
          currentMode.outExpr(expr);
        }
      }
      
      function clickExpr(event, expr) {
        event.stopPropagation();
        currentMode.clickExpr(expr);
      }
      
      function buildExprNodes() {
        function isExprNode(n) {
          return !!n.id && n.id.startsWith("expr_");
        }
        
        function childExprs(node) {
          var nodes = Array.from(node.getElementsByTagName("*"));
          nodes.push(node);
          return nodes.filter(isExprNode);
        }
        
        function exprTags(node) {
          var components = Array.from(node.children).filter(function(n) {return !isExprNode(n);});
          
          var res = [node];
          components.forEach(function(c) {
            res = res.concat(exprTags(c));
          });
          
          return res;
        }
        
        return childExprs(document).map(function(n) {
          var expr = new Expr(n, exprTags(n));
          n.onmouseover = function(event) { overExpr(event, expr); };
          n.onmouseout = function(event) { outExpr(event, expr); };
          n.onclick = function(event) { clickExpr(event, expr); };
          return expr;
        });
      }
      
      function resetAllExprsStyle() {
        allExprs.forEach(function(expr) {
          expr.resetStyle();
        });
      }
      
      function installMode(mode) {
        currentMode.uninstall();
        currentMode = mode;
        currentMode.install();
      }
      
      function similarEvents(a, b) {
        return !!a && !!b && a.type === b.type && a.target === b.target;
      }
      
      Array.prototype.split = function (f) {
        var matched = [],
            unmatched = [],
            i = 0,
            j = this.length;
      
        for (; i < j; i++){
          (f.call(this, this[i], i) ? matched : unmatched).push(this[i]);
        }
      
        return [matched, unmatched];
      };
      
      Array.prototype.resize = function(newSize, defaultValue) {
        while(newSize > this.length)
          this.push(defaultValue);
        this.length = newSize;
        return this;
      }

      document.getElementById('toIndent').innerHTML = 
        ScastieExports.indentAccordingToPosition($chainStart, '\\n' + document.getElementById('toIndent').innerHTML).substring(1);
        
      var lastEvent = undefined;

      var allExprs = buildExprNodes();
      
      var currentMode = new IdleMode();
      currentMode.install();
      
      var suggestions = $jsSuggestions
      
    </script>"""

    js + JsLoader + "<div id='toIndent'>" + top + "<span id='insert_rhs'></span>" + middle + "<span id='insert_lhs'></span>" + bot + "</div>"
  }
}