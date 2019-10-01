// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo
import ressort.lo._

import scala.collection.mutable.{HashMap, HashSet, LinkedHashMap}


private class SymInfo(val sym: SymLike, val scalarType: Scalar, val decAnchor: Anchor) {
  private var assignAnchor_ : Option[Anchor] = None
  private var otherNames_ : List[SymLike] = Nil

  var value: Option[Expr] = None

  def addName(name: SymLike): Unit = {
    otherNames_ = name :: otherNames_
  }

  def otherNames: List[SymLike] = otherNames_

  decAnchor.addDec(this)

  def assignAnchor: Option[Anchor] = assignAnchor_

  def assign(anchor: Anchor): Unit = {
    assignAnchor_ = Some(anchor)
    anchor.addAssign(this)
  }
}

/** Denotes a specific location in the original AST once type information is removed */
private class Anchor(val name: SymLike, val order: Int, val block: BlockScope) {
  var assignSyms = List[SymLike]()
  private var decSyms = List[SymLike]()

  def addDec(sym: SymInfo): Unit = { decSyms = sym.sym :: decSyms }

  def addAssign(sym: SymInfo) = { assignSyms = sym.sym :: assignSyms }

  def decs(temps: Map[SymLike, SymInfo]) = {
    decSyms.reverse.flatMap(temps.get(_)).map(si => Dec(si.sym, si.scalarType))
  }
  def assigns(temps: Map[SymLike, SymInfo]) = {
    assignSyms.reverse.flatMap(temps.get(_)).map(si => Assign(si.sym, (si.value.get)))
  }

  def declarePlaceholder = DecAssign(name, Index(), Const(0))
}

/** Scopes created by the beginning of a child block (function or for loop) */
private class BlockScope(val scope: Symtab, val parent: Option[BlockScope]) {
  private var anchors = Seq[Anchor]()

  /** Marks the beginning of the block, where declarations should be inserted */
  val topAnchor = newAnchor()

  /** The current point at which new assignments should be added */
  def curAnchor = anchors.head

  /** All anchors associated with this block */
  def allAnchors = anchors

  private def newAnchor(): Anchor = {
    val name = LoSym(new SymId("anchor"), BlockScope.anchorCount)
    BlockScope.anchorCount += 1
    val a = new Anchor(name, BlockScope.anchorCount, this)
    anchors = a +: anchors
    a
  }

  /** Returns the declaration for a new anchor, and sets `curAnchor` to it */
  def dropAnchor(): LoAst = newAnchor().declarePlaceholder
}

private object BlockScope {
  var anchorCount = 0

  /** Returns minimal scope dominated by all those in `blocks` */
  def minDominator(blocks: Seq[BlockScope]): BlockScope = {
    for (b <- blocks) {
      if (blocks.forall(b2 => b2.scope.dominates(b.scope)))
        return b
    }
    // No dominant scope was found, so try again with all scopes' parents
    minDominator(blocks.map(b => b.parent.getOrElse(b)))
  }

  /** Returns the minimal scope in `blocks` */
  def min(blocks: Traversable[BlockScope]): BlockScope = {
    var minScope = blocks.head
    for (b <- blocks) {
      if (minScope.scope.dominates(b.scope))
        minScope = b
    }
    minScope
  }
}

private class BlockStack {
  private val anchors = HashMap[SymLike, Anchor]()
  private var anchorMapBuilt = false
  private var stack = List[BlockScope]()
  private var blocks = List[BlockScope]()

  def push(scope: Symtab): BlockScope = {
    anchorMapBuilt = false
    val s = new BlockScope(scope, stack.headOption)
    anchors(s.topAnchor.name) = s.topAnchor
    blocks = s :: blocks
    stack = s :: stack
    s
  }

  def pop(): Unit = {
    stack = stack.tail
  }

  def isEmpty: Boolean = stack.isEmpty

  def top: BlockScope = stack.head

  def findAnchor(name: SymLike): Option[Anchor] = {
    if (!anchorMapBuilt) {
      for {
        b <- blocks
        a <- b.allAnchors
      } yield {
        anchors(a.name) = a
      }
      anchorMapBuilt = true
    }
    anchors.get(name)
  }
}

private class CommonSubExpressions(ast: TypedLoAst, safe: Boolean=true) {
  val stack = new BlockStack()
  var count = 0

  /** Value, type, and dependency information for symbols in the original AST */
  val info = HashMap[ScopedSym, SymInfo]()

  /** Value, type, and dependency information for newly-created temporaries */
  val temps = HashMap[SymLike, SymInfo]()

  /** A list of temps declared in each block scope */
  val tempsForScope = HashMap[BlockScope, List[SymInfo]]()

  /** Each expression encountered so far and given a symbolic name */
  val renamed = HashMap[Expr, SymLike]()

  /** The topmost scope, and the first one pushed onto the stack. */
  var topScope: BlockScope = null

  /** The current function scope, if inside one is the head */
  var funcScope: List[BlockScope] = Nil

  /** The scope at which to declare temporaries with const-only dependencies */
  def defaultScope: BlockScope = if (funcScope.nonEmpty) funcScope.head else topScope

  private lazy val tmap = temps.toMap

  /** Inserts temporary declarations and non-suppressed assignments to a replaced AST */
  def declare(ast: LoAst): LoAst = {
    val children = ast.astChildren.map(declare)
    val newChildren = ast.replaceAstChildren(children)
    newChildren match {
      case da @ DecAssign(s: SymLike, Index(_), Const(0)) => {
        val statements = stack.findAnchor(s).map { a =>
          val decs = a.decs(tmap)
          val assigns = a.assigns(tmap) map { a => if (safe) Assign(a.l, Safe(a.e)) else a }
          val lines = decs ++ assigns
          lines match {
            case Seq(s) => s
            case Seq() => Nop
            case _ => Block(lines.toList)
          }
        }
        statements.getOrElse(da)
      }
      case Block(c::Nil) => c
      case Block(ops) => Block(ops.filter(_!=Nop))
      case _ => newChildren
    }
  }

  /** Replaces any temps with ony a single usage by their original expressions */
  def noSingleUse(ast: LoAst): LoAst = {
    val useCounts = HashMap[SymLike, Int]()

    def countUsages(ast: LoAst): Unit = {
      def doExprs(e: Expr): Unit = e match {
        case s: SymLike if temps.contains(s) => {
          useCounts(s) = useCounts.getOrElse(s, 0) + 1
        }
        case _ => e.children.map(doExprs)
      }
      ast.exprChildren.map(doExprs)
      ast.astChildren.map(countUsages)
    }

    def replace(ast: LoAst): LoAst = {
      def replaceExprs(e: Expr): Expr = e match {
        case s: SymLike if temps.contains(s) => {
          val info = temps(s)
          // Bit of a hack here, because Phi() nodes might end up in LValue expressions
          // and so *must* remain a temp, as a SymLike is an LValue
          if (useCounts(s) <= 2 && !info.value.get.isInstanceOf[Phi]) {
            replaceExprs(info.value.get)
          } else {
            s
          }
        }
        case _ => e.replaceChildren(e.children.map(replaceExprs))
      }
      ast match {
        case Assign(s: SymLike, rhs) if temps.contains(s) => Assign(s, replaceExprs(rhs))
        case a: Assign  => Assign(a.l, replaceExprs(a.e))
        case d: DecAssign => DecAssign(d.sym, d.loType, replaceExprs(d.value))
        case _ => {
          val newCh = ast.replaceExprChildren(ast.exprChildren.map(replaceExprs))
          newCh.replaceAstChildren(newCh.astChildren.map(replace))
        }
      }
    }

    countUsages(ast)
    replace(ast)
  }

  /** Returns new temporary for this expression of AST `typed` if it is renamed */
  def rename(e: Expr, typed: TypedLoAst, inMux: Boolean=false): (Expr, Option[SymLike]) = {
    val newChildren = e match {
      case m: Mux => {
        // Mux is handled separately so that we can avoid renaming expressions with
        // side effects (array subscripts, dereferences) that should only be evaluated
        // conditionally.
        List(
          rename(e.children.head, typed, inMux),
          rename(e.children(1), typed, true),
          rename(e.children(2), typed, true)).map(_._1)
      }
      case _ => e.children.map(c => rename(c, typed, inMux)._1)
    }
    val newExpr = e.replaceChildren(newChildren)
    def containsSubscOrDeref(e: Expr): Boolean = e match {
      case s: Subsc => true
      case d: Deref => true
      case _ => e.children.map(containsSubscOrDeref).foldLeft(false)(_ || _)
    }
    def exclude(e: Expr) = e match {
      case c: Cast => true
      case True => true
      case False => true
      case _ if (containsSubscOrDeref(e) && inMux) => true
      case _ => false
    }

    val tempOpt = (newExpr, typed.scope(e).loType) match {
      case (_, Ptr(_, _)) => None
      case (_, Arr(_, _)) => None
      case (FakeUse(e2), _) => None
      case (Phi(_, _, _), _) => None
      case (_, s: Struct) => None
      case _ if renamed.contains(newExpr) => {
        // This expression has been given a name
        val tempInfo = temps(renamed(newExpr))
        Some(tempInfo.sym)
      }
      case _ if exclude(newExpr) => {
        None
      }
      case (_, scalar: Scalar) if !renamed.contains(newExpr) => {
        // This expression has not yet been assigned to a symbol, so make a temp

        // Find all the symbols on which the expression depends
        def dependencies(e: Expr): Seq[SymLike] = {
          e match { case s: SymLike => return Seq(s); case _ =>}
          val seqs = for (c <- e.children) yield {
            c match {
              case s: SymLike => Seq(s)
              case _ => c.children.map(dependencies).foldLeft(Seq[SymLike]())(_ ++ _)
            }
          }
          seqs.foldLeft(Seq[SymLike]())(_ ++ _)
        }
        val symDeps = dependencies(newExpr)
        // Extract info about the dependencies
        val depInfos: Seq[SymInfo] = dependencies(newExpr).map { s =>
          if (temps.contains(s))
            temps(s)
          else
            info(typed.scope.unique(s))
        }

        lazy val maxAssign: Anchor = {
          val assigns = depInfos.map(si => si.assignAnchor.getOrElse(si.decAnchor))
          val max = assigns.map(_.order).max
          // Can only be one value, since each order used exactly once
          assigns.filter(_.order == max).head
        }

        lazy val blockScope = {
          // Subscripts and pointer renames are only valid inside the block where they first occur
          // Since they have side effects, they can't be hoisted outside of if statements, etc.
          val dec = stack.top.topAnchor
          val assign = if (maxAssign.order > dec.order) maxAssign else dec
          (dec, assign)
        }

        // Determine which anchors at which to declare and assign the new temp
        val (decAnchor: Anchor, assignAnchor: Anchor) = e match {
          case _ if (depInfos.isEmpty) => (defaultScope.topAnchor, defaultScope.topAnchor)
          case _ if (containsSubscOrDeref(e)) => blockScope
          case _ => {
            val dec = {
              val nonConst = depInfos.filter(_.value.map(!_.isInstanceOf[ConstExpr]).getOrElse(true))
              val blocks = nonConst.map(_.decAnchor.block)
              if (nonConst.isEmpty) {
                defaultScope.topAnchor
              } else if (containsSubscOrDeref(newExpr)) {
                BlockScope.min(blocks).topAnchor
              } else {
                BlockScope.minDominator(blocks).topAnchor
              }
            }
            (dec, maxAssign)
          }
        }

        // Generate a new temp symbol name, and record its info in temps
        val temp = LoSym(new SymId(s"t$count"))
        count += 1
        val symInfo = new SymInfo(sym = temp, scalarType = scalar.setConst(false), decAnchor = decAnchor)
        symInfo.assign(assignAnchor)
        symInfo.value = Some(newExpr)
        temps(temp) = symInfo
        tempsForScope(decAnchor.block) = symInfo :: tempsForScope.getOrElse(decAnchor.block, Nil)

        // Perform the rename by changing the rename table
        renamed(newExpr) = temp
        renamed(temp) = temp

        Some(temp)
      }
      case _ => { None }
    }
    (tempOpt.getOrElse(newExpr), tempOpt)
  }


  def recordSymInfo(sym: SymLike, loType: LoType, scope: Symtab): Unit = {
    val scalar = loType.toScalar
    val symInfo = new SymInfo(sym, scalar,  stack.top.topAnchor)
    info(scope.unique(sym)) = symInfo
  }

  def replace(typed: TypedLoAst): LoAst = {
    def transLhs(l: LValue): LValue = {
      l match {
        case s: SymLike => s
        case s: Subsc => Subsc(transLhs(s.l), rename(s.n, typed)._1)
        case f: Field => Field(transLhs(f.lv), f.field)
        case d: Deref => Deref(transLhs(d.l))
        case u: UField => UField(transLhs(u.lv), u.field)
        case _ => { println(l); ???}
      }
    }

    /** Records assignment and possible rename information for an explicit assignment's symbol */
    def assign(lhs: LValue, rhs: Expr): (Expr, LoAst) = {
      val lhsInfo = info(typed.scope.unique(lhs.root))
      val (newExpr, tempOpt) = rename(rhs, typed)
      tempOpt.map { tempSym =>
        val tempBlock = temps(tempSym).decAnchor.block
        lhs match {
          case s: SymLike  => {
            renamed(lhs) = tempSym
            temps(tempSym).addName(s)
          }
          case _ =>
        }
      }
      val a = anchor()
      lhsInfo.assign(stack.top.curAnchor)
      (newExpr, a)
    }

    def anchor() = stack.top.dropAnchor()

    typed.ast match {
      case Assign(l: LoSym, p: Phi) => {
        val linfo = info(typed.scope.unique(l))
        val a = anchor()
        linfo.assign(stack.top.curAnchor)
        // Skip Phi() expressions because renaming into these would break DCE
        typed.ast + a
      }
      case Assign(l: LValue, e) => {
        val newLhs = transLhs(l)
        val (newRhs, a) = assign(newLhs, e)
        Assign(newLhs, newRhs) + a
      }
      case d @ Dec(sym, loType) => {
        recordSymInfo(sym, loType, typed.scope)
        d + anchor()
      }
      case da @ DecAssign(sym, loType, e) => {
        recordSymInfo(sym, loType, typed.scope)
        val (newRhs, a) = assign(sym, e)
        DecAssign(sym, loType, newRhs) + a
      }
      case HeapAlloc(l: LValue, length) => {
        //rename(l, Some(l.root))
        val a = anchor()
        val newLhs = transLhs(l)
        HeapAlloc(newLhs.toLValue, length.map(rename(_, typed)._1)) + a
      }
      case Free(l) => {
        val newLhs = transLhs(l)
        val a = anchor()
        Free(newLhs) + a
      }
      case AssignReturn(l, app) => {
        val a = anchor()
        val newLhs = transLhs(l)
        val newArgs = app.args.map(a => a._1 -> rename(a._2, typed)._1)
        val lhsInfo = info(typed.scope.unique(newLhs.root))
        lhsInfo.assign(stack.top.curAnchor)
        AssignReturn(newLhs, App(app.func, newArgs)) + a
      }
      case _ => {
        val dropTopAnchor = stack.isEmpty
        if (stack.isEmpty) { stack.push(typed.scope); topScope = stack.top }
        val newExprs =
          typed.ast.replaceExprChildren(
            typed.ast.exprChildren.map(e => rename(e, typed)._1))
        val a = anchor()
        val children = for (c <- typed.children) yield {
          if (c.scope != stack.top.scope && !typed.ast.isInstanceOf[Block]) {
            stack.push(c.scope)
            // Add info for any implicit symbols to this scope
            for (s <- c.scope.myScope) {
              val scoped = ScopedSym(s, c.scope)
              c.scope(s).loType match {
                case scalar: Scalar => {
                  info(scoped) = new SymInfo(s, scalar, decAnchor = stack.top.topAnchor)
                  info(scoped).assign(stack.top.curAnchor)
                }
                case _ =>
              }
            }
            // Set the function scope if this a function declaration
            typed.ast match {
              case f: FuncDec => funcScope = stack.top :: funcScope
              case _ =>
            }
            val newAst = stack.top.topAnchor.declarePlaceholder + replace(c)
            // Unmap the top block's temps' expressions from the remap table so they can be renamed again
            tempsForScope.get(stack.top.topAnchor.block).map(renamed --= _.flatMap(_.value))
            tempsForScope.get(stack.top.topAnchor.block).map(renamed --= _.flatMap(_.otherNames))
            stack.pop()
            // Pop from function scope if this is a function declaration
            typed.ast match {
              case f: FuncDec => funcScope = funcScope.tail
              case _ => 
            }
            newAst
          } else {
            replace(c)
          }
        }
        val newChildren = newExprs.replaceAstChildren(children)
        val withBlockAnchor = newChildren + a
        if (dropTopAnchor)
          stack.top.topAnchor.declarePlaceholder + withBlockAnchor
        else
          withBlockAnchor
      }
    }
  }
}

object CommonSubExpressions {
  def apply(ast: TypedLoAst, safe: Boolean=true): TypedLoAst = {
    val rt = new CommonSubExpressions(ast, safe)
    val newAst = rt.replace(ast)
    val dec = rt.declare(newAst)
    val finalAst = rt.noSingleUse(dec)
    TypedLoAst(finalAst)
  }
}
