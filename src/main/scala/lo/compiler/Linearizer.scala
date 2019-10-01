package ressort.lo.compiler
import ressort.lo._
import ressort.util
import scala.collection.mutable.LinkedHashSet
import scala.collection.immutable.ListMap

object Linearizer {
  case class DecRef(dec: FuncDec, scope: Symtab) {
    def rename(newName: String) = {
      FuncDec(Id(newName), dec.params, dec.body, dec.returnType)
    }
  }
  
  case class FuncRef(name: Id, scope: Symtab)
  
  /** Stores the mapping of func names to declarations.
    * 
    * `order` is used to track the order in which functions were
    * seen so as to preserve the dependencies between them in the emmitted 
    * linearization.
    */
  class FuncSet(
      val set: ListMap[String, List[DecRef]] = ListMap(), 
      val order: List[DecRef]= List()) {
    def +(func: DecRef) = {
      val funcs = {
        if(set.contains(func.dec.name.name))
          set(func.dec.name.name)
        else 
          Nil
      }
      val mapEntry = (func.dec.name.name -> (func::funcs))
      new FuncSet(set + mapEntry, func::order)
    }
    def +(list: List[DecRef]): FuncSet = {
      list.foldLeft(this) { 
        (funcSet, ref) => { funcSet + ref }
      }
    }
    def +(other: FuncSet): FuncSet = {
      other.set.foldLeft(this) { 
        (set, fm) => { set + fm._2 }
      }
    }
    def rename: ListMap[DecRef, FuncDec] = {
      def renameFunc(
          map: ListMap[DecRef, FuncDec], 
          name: String, 
          refs: List[DecRef]) = {
        val updates = (0 to refs.length-1) map { 
          i => {
            val newName = {
              if(i > 0)
                "__LIN__"+refs(i).dec.name.name+"_"+i
              else
                refs(i).dec.name.name
            }
            (refs(i) -> (refs(i).rename(newName)))
          }
        }
        updates.foldLeft(map) { (set, update) => set + update }
      }
      set.foldLeft(ListMap[DecRef, FuncDec]()) { 
        (map, fm) => renameFunc(map, fm._1, fm._2) 
      } 
    }
  }
  
  /** Replaces an App(Id()...) by one in which the target function is named
    * by a DecRef, rather than a Id.  Used for substitution after renaming.
    */
  case class RefApp(ref: FuncRef, args: Seq[(Id, Expr)]) extends FakeLoAst {
    override def replaceExprChildren(newChildren: List[Expr]): RefApp = {
      ??? // NOTE: indeterminacy of ordering in args map means this is broken,
      // .. but it's not clear why it would ever be called.  TODO
      copy(args = args.map(_._1).zip(newChildren.drop(1)))
    }
  }

  /** Replaces an AssignReturn(...) as RefApp does App() */
  case class RefAssignReturn(
      lv: LValue, 
      ref: FuncRef, 
      args: Seq[(Id, Expr)]) extends FakeLoAst {
    override def exprChildren: List[Expr] = {
      val argExprs = args map { _._2 }
      lv :: argExprs.toList
    }
    
    override def replaceExprChildren(newChildren: List[Expr]): RefAssignReturn = {
      ??? // NOTE: indeterminacy of ordering in args map means this is broken,
      // .. but it's not clear why it would ever be called.  TODO
      copy(lv = newChildren(0).toLValue, args = args.map(_._1).zip(newChildren.drop(1)))
    }
  }

  object BuildFuncSet extends TypedLoAstTransform {
    type T = FuncSet
    def trans(oldAst: TypedLoAst, children: List[XFormAst]) = {
      val newChildren = children map { c => c.newAst }
      // Can't add a FuncDec when it's the head of the current node, since
      // we need the scope of its parent (its own scope is Symtab.Empty :-( )
      val funcSet = children.foldLeft(new FuncSet()) { 
        (set, xf) => set + xf.payload
      }
     
      oldAst.ast match {
        case app: App => {
          val App(name, args) = replaceChildren(oldAst.ast, children)
          val ref = FuncRef(name, oldAst.scope.getEnclosing(name))
          XFormAst(RefApp(ref, args), funcSet)
        }
        case ar: AssignReturn => {
          val AssignReturn(lv, app) = ar
          val ref = FuncRef(app.func, oldAst.scope.getEnclosing(app.func))
          XFormAst(RefAssignReturn(lv, ref, app.args), funcSet)
        }
        case fd: FuncDec => {
          val newFd = replaceChildren(oldAst.ast, children).toFuncDec
          val ref = DecRef(newFd, oldAst.scope.getEnclosing(fd.name))
          XFormAst(replaceChildren(oldAst.ast, children), funcSet + ref)
        }
        case _ => {
          XFormAst(replaceChildren(oldAst.ast, children), funcSet)
        }
      }
    }
  }
  class ReplaceFuncs(map: ListMap[FuncRef, Id]) extends AstTransform {
    type T = Unit
    def trans(oldOp: LoAst, children: List[XFormAst]) = {
      val op = replaceChildren(oldOp, children)
      val newOp = op match {
        case fd: FuncDec => {
          Nop
        }
        case RefApp(funcRef, args) => App(map(funcRef), args)
        case RefAssignReturn(lv, funcRef, args) => {
          AssignReturn(lv, App(map(funcRef), args))
        }
        case App(_, _) => throw new AssertionError("APP NOT REPLACED: "+op)
        case other => other
      }
      XFormAst(newOp, ())
    }
  }

  /** Moves all typedefs before any new FuncDecs, which might
    * depend on them.
    */
  object PrependTypedefs extends AstTransform {
    type T = List[Typedef]
    
    def trans(oldOp: LoAst, children: List[XFormAst]) = {
      val op = replaceChildren(oldOp, children)
      val internalTypedefs = children.foldLeft(List[Typedef]()) {
        (list, child) => list ++ child.payload
      }
      op match {
        case td: Typedef => XFormAst(Nop, internalTypedefs ++ List(td))
        case _ => XFormAst(op, internalTypedefs)
      }
    }

    def apply(op: LoAst): LoAst = {
      val xop = dfTrans(op)
      Block(xop.payload) + xop.newAst
    }
  }

  
  def apply(top: TypedLoAst): TypedLoAst = {
    val xfop = BuildFuncSet.dfTrans(top)
    val newTOp = xfop.newAst
    val funcMap = xfop.payload
    val decMap: ListMap[DecRef, FuncDec] = funcMap.rename
    val renameMap: ListMap[FuncRef, Id] = decMap map { 
      case (decRef, funcDec) => (
        FuncRef(decRef.dec.name, decRef.scope) -> funcDec.name) 
    }
    val xform = new ReplaceFuncs(renameMap)
    val xformed = xform.dfTrans(newTOp)
    val funcDecs = (funcMap.order.reverse map { f => decMap(f) }).toList
    val xformedFuncs = funcDecs map { 
      dec => {
        val newBody = xform.dfTrans(dec.body).newAst
        FuncDec(dec.name, dec.params, newBody, dec.returnType)
      }
    }
    val newOp = PrependTypedefs(Block(xformedFuncs ::: List(xformed.newAst)))
    TypedLoAst(newOp)
  }

}
