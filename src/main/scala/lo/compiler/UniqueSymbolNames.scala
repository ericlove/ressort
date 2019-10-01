package ressort.lo.compiler
import ressort.lo._
import ressort.util
import scala.collection.mutable.{HashMap, LinkedHashSet}

/** Assigns a unique concrete name to each [[LoSym]] in the typed AST */
class UniqueSymbolNames(ast: TypedLoAst) extends TypedLoAstTransform {
  type T = Unit

  private val syms = new GetSymbolNames(ast)
  syms.dfTrans(ast)

  val usedNames = LinkedHashSet[Id]() ++ syms.usedNames
  val finalNames = HashMap[LoSym, Id]()

  for (s <- syms.namedSymbols) {
    var count = 0 
    var cand = if (syms.symbolsWithName(Id(s.name)).count(_=>true)> 1) {
      Id(s.name + count.toString)
    } else {
      Id(s.name)
    }
    while (usedNames.contains(cand)) {
      cand = Id(s.name + count.toString)
      count += 1
    }
    usedNames += cand
    finalNames(s) = cand
  }
 

  private object RenameSymbols extends ExprTransform {
    type T = Unit
    def trans(
        oldExpr: Expr,
        children: List[XFormExpr],
        scope: Symtab=Symtab.Empty) = {
      val newCh = replaceChildren(oldExpr, children)
      val newExpr = oldExpr match {
        case s: LoSym => {
          finalNames(s)
        }
        case _ => {
          newCh
        }
      }
      XFormExpr(newExpr, ())
    }
  }
  def trans(oldAst: TypedLoAst, children: List[XFormAst]) = {
    val newOldAst0 = replaceChildren(oldAst.ast, children)
    val newOldAst = transExprs(RenameSymbols, newOldAst0, oldAst.scope)
    val newAst = newOldAst match {
      case Dec(sym: LoSym, t) => Dec(finalNames(sym), t)
      case DecAssign(sym: LoSym, t, v) => DecAssign(finalNames(sym), t, v)
      case f: ForLoopLoAst => {
        f.index match {
          case s: LoSym => f.withIndex(finalNames(s))
          case _ => f
        }
      }
      case _ => newOldAst
    }
    XFormAst(newAst, ())
  }
}

object UniqueSymbolNames {
  def apply(ast: TypedLoAst): TypedLoAst = {
    val usn = new UniqueSymbolNames(ast)
    val newAst = usn.dfTrans(ast).newAst
    TypedLoAst(newAst)
  }
}

/** Finds all the [[Id]]s and [[LoSym]]s used in the given AST */
class GetSymbolNames(ast: TypedLoAst) extends TypedLoAstTransform {
  val namedSymbols = LinkedHashSet[LoSym]()

  val usedNames = LinkedHashSet[Id]()

  val symbolsWithName = HashMap[Id, LinkedHashSet[LoSym]]()

  type T = Unit

  def checkExpr(expr: Expr): Unit = {
    expr match {
      case i: Id => { usedNames += i }
      case s: LoSym => {
        namedSymbols += s
        symbolsWithName(Id(s.name)) = symbolsWithName.getOrElse(Id(s.name), LinkedHashSet[LoSym]()) + s
      }
      case _ =>
    }
  }

  private object ExamineSymbols extends ExprTransform {
    type T = Unit
    def trans(
        oldExpr: Expr,
        children: List[XFormExpr],
        scope: Symtab=Symtab.Empty) = {
      val newCh = replaceChildren(oldExpr, children)
      checkExpr(oldExpr)
      XFormExpr(oldExpr, ())
    }
  }
  def trans(oldAst: TypedLoAst, children: List[XFormAst]) = {
    transExprs(ExamineSymbols, oldAst.ast, oldAst.scope)
    val newAst = oldAst.ast match {
      case Dec(sym: LoSym, t) => checkExpr(sym)
      case DecAssign(sym: LoSym, t, v) => checkExpr(sym)
      case f: ForLoopLoAst => {
        f.index match {
          case s: LoSym => checkExpr(s)
          case _ => f
        }
      }
      case _ =>
    }
    XFormAst(oldAst.ast, ())
  }
}

