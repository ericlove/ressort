// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._
import scala.collection.mutable.{HashMap, LinkedHashMap, HashSet}

class StaticSingleAssignment(ast: TypedLoAst) {

  private class RenamedSym(var newSym: LoSym, val loType: LoType) {
    private var numUsages = 0

    var aliasFor = List[ScopedSym]()

    def next(): LoSym = {
      numUsages += 1
      val n = newSym.copy(n = numUsages)
      newSym = n
      n
    }
  }

  /** Scope and declaration information about each renamed symbol */
  private val syms = HashMap[ScopedSym, RenamedSym]()

  /** Maps each renamed symbol to its original */
  private val origSyms = HashMap[LoSym, ScopedSym]()

  /** Carry upwards a map of symbols that get updated in each block to their new names */
  case class XFormAst(newAst: LoAst, rmap: RMap)

  /** Saves the internal (child) scope of each [[FuncDec]] */
  private val funcScopes = HashMap[FuncDec, Symtab]()

  /** Abbreviation for "rename map", which tells the names of symbols in the current context */
  private type RMap = Map[ScopedSym, LoSym]

  class ExprRenamer(rmap: RMap) extends ExprTransform {
    type T = Unit

    def trans(oldExpr: Expr, children: List[XFormExpr], scope: Symtab=Symtab.Empty) = {
      val newCh = replaceChildren(oldExpr, children)
      val newExpr = newCh match {
        case s: SymLike => {
          val scoped = scope.unique(s)
          val symConv = rmap.getOrElse(scoped, s)
          symConv
        }
        case _ => newCh
      }
      XFormExpr(newExpr, ())
    }
  }

  def rename(scoped: ScopedSym, rmap: RMap, loType: Option[LoType]=None) = {
    val newSym = if (syms.contains(scoped)) {
      val init = syms(scoped)
      val next = syms(scoped).next()
      val rn = new RenamedSym(next, init.loType)
      next
    } else {
      val init = LoSym(new SymId(scoped.sym.name))
      val typeInfo = loType match {
        case Some(scalar: Scalar) => scalar.setConst(false)
        case Some(t) => t
        case None if syms.contains(scoped) => syms(scoped).loType
        case None => {
          scoped.scope(scoped.sym).loType match {
            case s: Scalar => s
            case other => println(s"Can't handle ${scoped.sym} of type $other"); ???
          }
        }
      }
      val renamed = new RenamedSym(init, typeInfo)
      syms(scoped) = renamed
      renamed.newSym
    }
    origSyms(newSym) = scoped
    Map(scoped -> newSym)
  }


  /** Traverses the transformed dag (result of [[trans]]) to insert declaration chains
    *
    * A declaration chain consists of declarations for all the [[LoSym]]s created for a
    * particular original [[ScopedSym]] in the course of its SSA updates.
    */
  def insertDecs(orig: LoAst): LoAst = {
    def decChain(s: ScopedSym): LoAst = {
      if (!syms.contains(s)) {
        return Nop
      }
      val last = syms(s).next()
      val decs = (0 to last.n).map(n => Dec(last.copy(n=n), syms(s).loType))
      Block(decs.toList)
    }
    orig match {
      case Dec(s: LoSym, loType) if origSyms.contains(s) => {
        decChain(origSyms(s))
      }
      case fd: FuncDec => {
        val scope = funcScopes(fd)

        val chains = fd.params.map(p => scope.unique(p._1)).map(decChain)
        val decs = chains.foldLeft[LoAst](Nop)(_ + _)
        val body = insertDecs(fd.body)
        fd.copy(body = decs + body)
      }
      case _ => {
        val newChildren = orig.astChildren.map(insertDecs)
        orig.replaceAstChildren(newChildren)
      }
    }
  }


  /** Performs a pre-order replacement of AST node children 
    * (Unlike a [[TypedLoAstTransform]], which defaults to post-order).
    */
  def trans(orig: TypedLoAst, rmap: RMap): XFormAst = {
    val renamer = new ExprRenamer(rmap)
    val newOldAst = renamer.transExprs(orig.ast, orig.scope)

    def chainUpdateAssign(old: SymLike, next: SymLike): LoAst = {
      Assign(next, old) + UseSym(old, next)
    }

    def chainUpdate(scoped: ScopedSym): (LoAst, RMap) = {
      val orig: LoSym = syms(scoped).newSym
      val update = rename(scoped, rmap)
      val assign = chainUpdateAssign(orig, update(scoped))
      (assign, update)
    }

    newOldAst match {
      case DecAssign(s: SymLike, loType: LoType, e: Expr) => {
        assert(orig.children.isEmpty)
        val scoped = orig.scope.unique(s)
        val update: RMap = rename(scoped, rmap, Some(loType))
        val newAst = Dec(update(scoped), loType) + Assign(update(scoped), e)
        XFormAst(newAst, update)
      }
      case Dec(l: SymLike, loType: LoType) => {
        assert(orig.children.isEmpty)
        val scoped = orig.scope.unique(l)
        val update = rename(scoped, rmap, Some(loType))
        XFormAst(Dec(update(scoped), loType), update)
      }
      case Assign(_ : LoSym, e) => {
        assert(orig.children.isEmpty)
        val oldSym = orig.ast.asInstanceOf[Assign].l.asInstanceOf[SymLike]
        val scoped = orig.scope.unique(oldSym)
        val update = rename(scoped, rmap)
        val newAst = Assign(update(scoped), e)
        XFormAst(newAst, update)
      }
      case Assign(l: LValue, e) => {
        val oldRoot = orig.ast.asInstanceOf[Assign].l.root
        val scoped = orig.scope.unique(oldRoot)
        val update = rename(scoped, rmap)
        val newLv = l.withRoot(update(scoped))
        val rootInfo = syms(scoped)
        val aliasOrigs = rootInfo

        var updates = update
        var newAst = chainUpdateAssign(l.root, newLv.root) + Assign(newLv, e)
        for (scoped <- rootInfo.aliasFor) {
          val orig: LoSym = syms(scoped).newSym
          val (assign, update) = chainUpdate(scoped)
          updates ++= update
          newAst += assign + UseSym(orig, newLv.root)
        }
        XFormAst(newAst, updates)
      }
      case UseSym(observer: SymLike, input: SymLike) => {
        val isym = orig.ast.asInstanceOf[UseSym].input
        val iscoped = orig.scope.unique(isym)
        val isymInfo = syms(iscoped)
        val osym = orig.ast.asInstanceOf[UseSym].observer
        val oscoped = orig.scope.unique(osym)
        if (!isymInfo.aliasFor.contains(oscoped))
          isymInfo.aliasFor ::= oscoped
        val (assign, update) = chainUpdate(oscoped)
        val newAst = UseSym(rmap(oscoped), rmap(iscoped)) + assign
        XFormAst(newAst,  update)
      }
      case loop: ForLoopLoAst => {
        val cscope = orig.children.head.scope
        val isym = cscope.unique(loop.index)
        val index = rename(isym, rmap, Some(Index()))(isym)
        val loopSyms = loopUpdates(cscope).filter(s => !cscope.dominates(s.scope)).toSeq // Symbols updated inside this loop
        val origSyms = loopSyms.map(s => s -> syms(s).newSym).toMap
        val initSyms = loopSyms.map(s => syms(s).next())
        val lmap = rmap ++ Map(isym -> index) ++ loopSyms.zip(initSyms).toMap
        val XFormAst(newBody, updates) = trans(orig.children.head, lmap)
        val finalSyms = loopSyms.map(updates)
        val newAst = loop.withIndex(index).replaceAstChildren(List(newBody)).asInstanceOf[ForLoopLoAst]
        val initPhis = for ((scoped, init) <- loopSyms.zip(initSyms)) yield {
          val rsym = rmap(scoped)
          val fsym = updates(scoped)
          val osym = origSyms(scoped)
          val initPhi = Assign(init, Phi(Equal(newAst.index, newAst.min), rsym, fsym))

          initPhi
        }

        val innerUpdates = updates.filter(s => !cscope.dominates(s._1.scope))
        val phisAndUpds = for ((scoped, lastLoop) <- innerUpdates) yield {
          val osym = origSyms.getOrElse(scoped, lastLoop)
          val fsym = updates(scoped)
          val nsym = syms(scoped).next()
          val finalPhi = Assign(nsym, Phi(loop.max > loop.min, osym, fsym))

          val upd = scoped -> nsym
          (finalPhi, upd)
        }
        val finalPhis = phisAndUpds.map(_._1)
        val finalUpdates = phisAndUpds.map(_._2)

        val finalAst = newAst.withBody(Block(initPhis.toList) + newAst.body) + Block(finalPhis.toList)
        XFormAst(finalAst, finalUpdates.toMap)
      }
      case IfElse(cond, ifBody, elseBody) => {
        val XFormAst(newIf, ifUpdates) = trans(orig.children(0), rmap)
        val XFormAst(newElse, elseUpdates)  = trans(orig.children(1), rmap)
        val ifMap = ifUpdates.filter(u => u._1.scope.dominates(orig.scope))
        val elseMap = elseUpdates.filter(u => u._1.scope.dominates(orig.scope))
        val common = ifMap.keys.toSet & elseMap.keys.toSet
        def phi(targ: SymLike, ifSym: SymLike, elseSym: SymLike): LoAst = {
          val cs = LoSym(new SymId("cond"))
          DecAssign(cs, Bool(), cond) +
            Assign(targ, (Phi(cs, ifSym, elseSym)))
        }
        val both = for (sym <- common) yield {
          val next = rename(sym, rmap)
          val assign = phi(next(sym), ifMap(sym), elseMap(sym))
          XFormAst(assign, next)
        }
        val ifOnly = for (sym <- ifMap.keys.toSet -- elseMap.keys.toSet) yield {
          val next = rename(sym, rmap)
          XFormAst(phi(next(sym), ifMap(sym), rmap(sym)), next)
        }
        val elseOnly = for (sym <- elseMap.keys.toSet -- ifMap.keys.toSet) yield {
          val next = rename(sym, rmap)
          XFormAst(Assign(next(sym), Phi(Not(cond), elseMap(sym), rmap(sym))), next)
        }
        val all = (ifOnly ++ elseOnly ++ both)
        val newAst = {
          IfElse(cond, newIf, newElse) +
            Block(all.map(_.newAst).toList)
        }
        val allUpdates = all.map(_.rmap).foldLeft(Map[ScopedSym, LoSym]())(_ ++ _)
        XFormAst(newAst, ifMap ++ elseMap ++ allUpdates)
      }

      case w: While => ???
      case _ => {
        var curRmap = rmap
        val xforms = for (c <- orig.children) yield {
          val newc = trans(c, curRmap)
          curRmap = curRmap ++ newc.rmap
          newc
        }
        val newAst = newOldAst.replaceAstChildren(xforms.map(_.newAst))
        val updates = xforms.map(_.rmap).foldLeft(Map[ScopedSym, LoSym]())(_ ++ _)
        newAst match {
          case fd: FuncDec => {
            // Need to save the original scope of the parameters
            // so they can be used for final `Dec` insertion
            val scope = orig.children.head.scope
            funcScopes(fd) = scope
          }
          case _ =>
        }
        XFormAst(newAst, updates)
      }
    }
  }

  /** A list of all [[SymLike]]s updated in each for/while loop
    * (as identified by their child scopes).
    */
  private val loopUpdates: Map[Symtab, Set[ScopedSym]] = {
    val lmap = HashMap[Symtab, Set[ScopedSym]]()

    def walk(tast: TypedLoAst): Set[ScopedSym] = {
      val childUpdates = {
        val updates = tast.children.map(walk).foldLeft(Set[ScopedSym]()) (_ ++ _)
        updates.filter(s =>
          tast.scope.symType(s.sym).nonEmpty && tast.scope.getEnclosing(s.sym) == s.scope)
      }
      tast.ast match {
        case f: ForLoopLoAst => {
          val cscope = tast.children.head.scope
          lmap(cscope) =
            childUpdates
              .filter(s =>
                cscope.symType(s.sym).nonEmpty && cscope.getEnclosing(s.sym) == s.scope)
          childUpdates
        }
        case Assign(l: LValue, _) => {
          val s: SymLike = l.root
          val scoped = ScopedSym(s, tast.scope.getEnclosing(s))
          Set(scoped)
        }
        case w: While => {
          val cscope = tast.children.head.scope
          lmap(cscope) = childUpdates
          childUpdates
        }
        case _ => childUpdates
      }
    }

    walk(ast)
    lmap.toMap
  }
}

object StaticSingleAssignment {
  def apply(ast: TypedLoAst): TypedLoAst = {
    val ssa = new StaticSingleAssignment(ast)
    val newAst = ssa.trans(ast, Map()).newAst
    val withDecs = ssa.insertDecs(newAst)
    TypedLoAst(withDecs)
  }

  def collapse(typed: TypedLoAst): TypedLoAst = {
    val declared = HashSet[SymId]()
    val renamed = HashMap[LoSym, LoSym]()
    def build(typed: TypedLoAst): Unit = {
      typed.ast match {
        case Assign(s1: LoSym, Phi(_, s2: LoSym, _)) => renamed(s1) = s2
        case _ => typed.children.map(build)
      }
    }
    def transform(typed: TypedLoAst): LoAst = {
      def collapseExprs(e: Expr): Expr = {
        val newCh = e.children.map(collapseExprs)
        val withNewCh = e.replaceChildren(newCh)
        withNewCh match {
          case LoSym(id, _) => LoSym(id, 0)
          case Mux(cond, e1, e2) if e1 == e2 => e1
          case FakeUse(e) => e
          case _ => withNewCh
        }
      }
      val newCh = typed.children.map(transform)
      val withNewCh = typed.ast.replaceAstChildren(newCh)
      val newExprs = withNewCh.exprChildren.map(collapseExprs)
      val withNewExprs = withNewCh.replaceExprChildren(newExprs)
      withNewExprs match {
        case Assign(l: LoSym, FakeUse(l2: LoSym)) => Nop
        case Assign(l, e) if l == e => Nop
        case Assign(l, Phi(_, e1, e2)) if e1 == e2 => Nop
        case Assign(l, p: Phi)  => Nop
        case Dec(LoSym(id, n), t) if !declared.contains(id) =>
          declared += id
          Dec(LoSym(id, 0), t)
        case f @ ForSeq(LoSym(id, _), _, _, _, _) => f.withIndex(LoSym(id, 0))
        case f @ ForPar(LoSym(id, _), _, _, _, _) => f.withIndex(LoSym(id, 0))
        case _ => withNewExprs
      }
    }
    build(typed)
    val xform = transform(typed)
    TypedLoAst(xform)
  }
}
