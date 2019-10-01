// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._
import ressort.util
import scala.collection.mutable.HashMap

/** Represents the ''seen-by'' relationships between all symbols in `ast`.
  *
  * @param ast A [[LoAst]] that has had all [[SymLike]]s replaced by [[IntSym]]s
  * @param origSymNames The original [[SymLike]]s correponding to each [[IntSym]] in `ast`
  */
class AstDataflowGraph(val ast: LoAst, val seenBy: SeenByTable, val origSymNames: Array[SymLike]) {
  /** Returns a copy of `ast` where all [[IntSym]]s have been replaced by their original [[SymLike]]s */
  def withOrigSyms(ast: LoAst): LoAst = {
    def transExprs(e: Expr): Expr = e match {
      case IntSym(i) => origSymNames(i)
      case _ => e.replaceChildren(e.children.map(transExprs))
    }
    val newCh = ast.replaceAstChildren(ast.astChildren.map(withOrigSyms))
    val newEx = newCh.replaceExprChildren(newCh.exprChildren.map(transExprs))
    newEx match {
      case Dec(IntSym(i), loType) => Dec(origSymNames(i), loType)
      case DecAssign(IntSym(i), loType, value) => DecAssign(origSymNames(i), loType, value)
      case f: ForLoopLoAst => {
        val newIndex = origSymNames(f.index.asInstanceOf[IntSym].i)
        f.withIndex(newIndex)
      }
      case _ => newEx
    }

  }
}

object AstDataflowGraph {
  /** The symbol denoting output: anything that flows to this will be preserved */
  val TopIntId: Int = 0

  def asIndex(s: SymLike): Integer = s.root match {
    case IntSym(ind) => ind
    case _ => AstDataflowGraph.TopIntId
  }

  def apply(ta: TypedLoAst): AstDataflowGraph = {
    val b = new DataflowGraphBuilder(ta)
    b.graph
  }
}

/** Holds all observer information for each [[Integer]] seen in a
  * dataflow graph.
  *
  * If `sbt` is a [[SeenByTable]], and `sym` is an [[Integer]], then
  * `sbt(sym)` is the set of [[Integer]]-named symbols seen by `sym` in some AST.
  *
  * @note This is a mutable data structure used while building a 
  *       dataflow graph for an AST.  After construction, an immutable
  *       [[Map]] returned by `getMap()` should be used for all other ends.
  */
class SeenByTable(
    val origSymNames: Array[SymLike],
//    val renamedFuncParams: HashMap[Id, Seq[Integer]],
    renamed: HashMap[ScopedSym, Integer]) {
  val table = Array.fill[Set[Integer]](origSymNames.size) { Set[Integer]() }

  /** Adds the given set of observer [[Integer]]s to the entry for
    * `sym` in the seen-by table, creating a new entry for `sym` if needed.
    */
  def addObservers(sym: Integer, observers: Set[Integer]): Unit = {
    table(sym) ++= observers
  }

  /** Returns an indented string representation of the seen-by map.
    *
    * @param ast Includes the AST in string dump if supplied.
    */
  def tableStr(indent: Int = 0, ast: Option[LoAst] = None): String = {
    var str = ""
    line("Seen-by Table:")
    def line(s: String): Unit = { str += ("  "*indent) + s + "\n" }
    ast map { a =>
      line("for:\n" + a.lines(2).toString)
      line("::")
    }
    for ((s, i) <- table.zipWithIndex) {
      line(s"   $i : ${origSymNames(i)}:")
      for (o <- s) {
        line(s"      -> $o : ${origSymNames(o)}")
      }
    }
    str
  }

  /** Original scoped symbol of each index (used by tester) */
  lazy val invertedRename: Array[ScopedSym] = {
    val arr = new Array[ScopedSym](origSymNames.length)
    for ((s, i) <- renamed) {
     arr(i) = s
    }
    arr
  }

  /** Returns the set of observers for the given [[ScopedSym]] or throws
    * an exception if it is not in the table.
    */
  def apply(sym: ScopedSym): Set[ScopedSym] = {
    table(renamed(sym)).map(invertedRename(_))
  }
}

class DataflowGraphBuilder(orig: TypedLoAst)  {
  private val TopIntId = AstDataflowGraph.TopIntId

  /** The index of each renamed [[ScopedSym]] after conversion to an [[IntSym]] */
  private val renamed = new HashMap[ScopedSym, Integer]()
  renamed(Symtab.Empty.TopId) = AstDataflowGraph.TopIntId

  /** The integer symbol indices of the parameters of reach [[FuncDec]]
    *
    * This is needed because the parameters of functions can't be replaced by [[IntSym]]s
    */
  //private val renamedFuncParams: HashMap[Id, Map[Id, Integer]]()

  private val (withIntSyms, origSymNames) = {
    var count = 0

    def rename(sym: ScopedSym): Integer = {
      if (renamed.contains(sym)) {
        renamed(sym)
      } else {
        // Make sure the first real symbol starts at 1, as the 0th is reserved for `TopIntId`
        count += 1
        renamed(sym) = count
        count
      }
    }

    def trans(ast: TypedLoAst): LoAst = {
      val newCh = ast.ast.replaceAstChildren(ast.children.map(trans))
      def transExprs(e: Expr): Expr = e match {
        case i: IntSym => i
        case s: SymLike => IntSym(rename(ast.scope.unique(s)))
        case _ => e.replaceChildren(e.children.map(transExprs))
      }
      val newEx = newCh.replaceExprChildren(newCh.exprChildren.map(transExprs))
      newEx match {
        case Dec(sym, loType) => Dec(IntSym(rename(ast.scope.unique(sym))), loType)
        case DecAssign(sym, loType, value) => DecAssign(IntSym(rename(ast.scope.unique(sym))), loType, value)
        case f: ForLoopLoAst => {
          f.withIndex(IntSym(rename(ast.children.head.scope.unique(f.index))))
        }
        case _ => newEx
      }
    }

    val newAst = trans(orig)
    val origSymNames = {
      val a = new Array[SymLike](count+1)
      for ((s, n) <- renamed) {
        a(n) = s.sym
      }
      a
    }
    (newAst, origSymNames)
  }

  private val sbt: SeenByTable = new SeenByTable(origSymNames, renamed)

  /** The dataflow graph built by this builder. */
  val graph: AstDataflowGraph = {
    def build(ast: LoAst): Set[Integer] = {
      val updatedInChildren = {
        val cupdates = ast.astChildren.map(build)
        cupdates.foldLeft(Set[Integer]()) { _ ++ _ }
      }
      updatedInChildren ++ updateSeenBy(ast, updatedInChildren)
    }
    build(withIntSyms)
    new AstDataflowGraph(withIntSyms, sbt, origSymNames)
  }


  /** Updates the `SeenBy` table to reflect the flow at this node.
    *
    * @return The set of [[Integer]]s updated at `ast` itself (not its children).
    */
  private def updateSeenBy(ast: LoAst, updatedInChildren: Set[Integer]): Set[Integer] = {
    lazy val usages = findUsages(ast)

    def update(lv: LValue): Set[Integer] = {
      val sym = AstDataflowGraph.asIndex(lv.root)
      for (u <- usages) {
        sbt.addObservers(u, Set(sym))
      }
      Set(sym)
    }

    def updateApp(a: App) = {
      // Right now, the conservative strategy is to mark each symbol
      // that appears in the call as being seen by all others.
      for (sym <- usages) {
        sbt.addObservers(sym, usages)
      }
      usages
    }

    // These are the only AST node types that create data flows.
    ast match {
      case Assign(l, _)       => update(l)
      case DecAssign(l, _, _) => update(l)
      case UseSym(o, i)       => update(o)
      case HeapAlloc(l, _)    => update(l)
      case AssignReturn(l, a) => update(l) ++ updateApp(a)
      case r @ Return(e) => {
        // Symbols inside the returned expression are considered to flow to the program's output,
        // which is denoted by the symbol `TopIntId`
        for (u <- usages) {
          sbt.addObservers(u, Set(TopIntId))
        }
        Set(TopIntId)
      }
      case a @ App(_, _) => updateApp(a)
      case p: Printf => {
        //println(s"stmt:\n\t$p\nexprUsages:\n\t$exprUsages")
        for (u <- usages) {
          sbt.addObservers(u, Set(TopIntId))
        }

        Set(TopIntId)
      }
      case ie: IfElse => {
        // Symbols that appear in the conditional expression a considered to be seen by any
        // symbols updated in the if-body and else-body.
        val condUsages = findUsages(Return(ie.cond)) // Use Return() to get expressions without body
        for (u <- condUsages) {
          sbt.addObservers(u, updatedInChildren)
        }
        Set()
      }
      case f: ForLoopLoAst => {
        // Symbols that appear in the loop bound are considered to be seen by any symbols
        // updated in the loop body.
        val boundUsages = findUsages(f.withBody(Nop))
        for (u <- boundUsages) {
          sbt.addObservers(u, updatedInChildren)
        }
        Set(f.index.asInstanceOf[IntSym].i)
      }
      case a: ArrOp => {
        val sym = AstDataflowGraph.asIndex(a.opArr.root)
        for (u <- usages) {
          sbt.addObservers(u, Set(sym))
        }
        Set(sym)
      }
      case f: FuncDec => Set(TopIntId)
      case _ => Set()
    }
  }

  /** Returns the set of all integer-symbols s in the given AST node. */
  private def findUsages(ast: LoAst): Set[Integer] = {
    var usages = Set[Integer]()
    def walk(ast: LoAst) {
      ast.astChildren.map(walk)
      ast.exprChildren.map(walkExpr)
    }

    def walkExpr(e: Expr): Unit = e match {
      case IntSym(i) => usages += i
      case _ => e.children.map(walkExpr)
    }

    walk(ast)
    usages.toSet
  }
}