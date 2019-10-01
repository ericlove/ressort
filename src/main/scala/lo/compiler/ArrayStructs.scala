/** ArrayStructs: an LoRes transformation to convert all Arr(..) types into
  * structs that explicitly contain a length field.
  */
package ressort.lo.compiler
import ressort.lo._
import ressort.util
import scala.collection.mutable.{LinkedHashSet, LinkedHashMap}
import scala.collection.immutable.ListMap


object ExprStructs extends ExprTransform {
  type T = Unit
  def trans(
    oldExpr: Expr, 
    children: List[XFormExpr],
    scope: Symtab=(new Symtab()) ) = {
    val newCh = replaceChildren(oldExpr, children)
    val newExpr = oldExpr match {
      case Subsc(e, n) => {
        scope(e).loType match {
          case Arr(_, _) => {
            val newField = Deref(Field(children(0).newExpr.toLValue, 'items))
            Subsc(newField, children(1).newExpr)
          }
          case other => newCh
        }
      }
      case NumEntries(e) => scope(e).loType match {
        case Arr(_, _) => Field(children(0).newExpr.toLValue, 'len)
        case other => newCh
      }
      case other => newCh
    }
    XFormExpr(newExpr, ())
  }


  // In the case where the type of the whole old AST (i.e. the type at the 
  // root) is an Arr() type, convert the whole expression 
  // e to Deref(e.items).  This handles Array Ops.
  override def transRoot(
      oldExpr: Expr,
      children: List[XFormExpr],
      scope: Symtab=(new Symtab())) = {
    val oldXop = trans(oldExpr, children, scope)
    val newExpr = scope(oldExpr).loType match {
      case Arr(_, _) => Deref(Field(oldExpr.toLValue, 'items))
      case other => oldXop.newExpr
    }
    XFormExpr(newExpr, oldXop.payload)
  }
}

object ArrayStructs  {
  def apply(ast: TypedLoAst): TypedLoAst = {
    val as = new ArrayStructs()
    val erOp = ExplicitRanges(ast)
    val newOp = as.dfTrans(erOp).newAst
    val SplitLoRes(defs, code) = {
      // Since the typedefs generated in this transform will depend on some
      // already inside the AST (and vice versa), we need to combine them all
      // and then re-order them topologically using SplitLoRes
      val newDefs = as.getTypedefs
      SplitLoRes(newDefs + newOp)
    }
    TypedLoAst(defs + code)
  }
}

class ArrayStructs extends TypedLoAstTransform { 
  import ArrayStructs._
  val asPrefix = "_arr_"
  val tmpIds = new TempIds(asPrefix)

  type T = Unit

  val typeSet: LinkedHashSet[Typedef] = LinkedHashSet()
 

  // TODO: Change LoRes to allow assignment to all const fields of a Struct
  // at initialization to that the length and items pointer can be const.
  def irArrStruct(t: Data, const: Boolean=false): Struct = {
    val res = Struct(
      Id(asPrefix+(t.mangledName)),
      List('items -> Ptr(Arr(t, const), const=false), 'len -> Index(false)),
      const=const)
    res
  }

  def trans(oldAst: TypedLoAst, children: List[XFormAst]) = {
    val newExprsOp = transExprs(ExprStructs, oldAst.ast, oldAst.scope)
    val newOldAst = replaceChildren(newExprsOp, children)
    val newAst = newOldAst match {
      case Dec(sym, loType) => Dec(sym, transLoType(loType))
      case DecAssign(sym, loType, value) => {
        DecAssign(sym, transLoType(loType), value)
      }
      case HeapAlloc(l, Some(len)) => {
        val loType = oldAst.exprChildren.head.loType match {
          case Ptr(t, _) => t
          case _ => ???
        }
        HeapAlloc(l) + initArr(Deref(l), loType, len)
      }
      case FuncDec(name, params, body, returnType) => {
        transFuncDec(oldAst.scope, name, params, body, returnType)
      }
      case Typedef(struct) => Typedef(transLoType(struct).toStruct)
      case Free(lv) => transFree(oldAst.scope, lv)
      case other => other
    }
    XFormAst(newAst, ())
  }
  
  def initArr(l: LValue, loType: LoType, length: Expr) = {
    def allocLVal(lv: LValue, loType: LoType): LoAst = {
      loType match {
        case Arr(t2, _) => {
          val len = lv.dot('len)
          HeapAlloc(lv.dot('items), Some(len))
        }
        case Struct(name, fields, _) => {
          val fieldAllocs = {
            fields map { case (v, t) => allocLVal(lv.dot(v), t) }
          }
          Block(fieldAllocs.toList)
        }
        case other => Nop
      }
    }
    val i = tmpIds.newId("i")
    Assign(Field(l, 'len), length) + allocLVal(l, loType)
  }

  def transFuncDec(
      scope: Symtab, 
      name: Id, 
      params: Seq[(Id, Primitive)],
      body: LoAst,
      returnType: Option[Primitive]) = {
    val typedParams = params map { 
      case (v,t) => v -> transLoType(t).toPrimitive
    }
    val newReturnType = returnType match {
      case Some(t) => Some(transLoType(t).toPrimitive)
      case None => None
    }
    FuncDec(name, typedParams, body, newReturnType)
  }

  def transFree(scope: Symtab, lv: LValue) = {
    val oldIrType = scope(lv).loType
    oldIrType match {
      case Ptr(Arr(_, _), _) => {
        val freeItems = Free(Deref(lv).dot('items))
        val freeStruct = Free(lv)
        freeItems + freeStruct
      }
      case _ => Free(lv)
    }
  }

  def transLoType(loType: LoType): LoType = {
    loType match {
      case Ptr(t, c) => Ptr(transLoType(t), c)
      case Arr(t, c) => {
        val arrStruct = irArrStruct(transLoType(t).toData)
        val typedef = Typedef(arrStruct)
        if(!typeSet.contains(typedef))
          typeSet += typedef
        arrStruct
      }
      case Struct(name, fields, const) => {
        val newFields = fields map {
          case (f,t) => f -> transLoType(t).toComplete
        }
        Struct(name, newFields, const)
      }
      case sr: SplitRecord => {
        val newGroups = for (g <- sr.groups) yield {
          val newFields = for (f <- g.fields) yield {
            Record.Field(transLoType(f.loType).toNonRec, f.name)
          }
          Record.Group(newFields:_*)
        }
        sr.copy(groups = newGroups)
      }
      case fr: FlatRecord => {
        val newFields = for (f <- fr.fields) yield {
          Record.Field(transLoType(f.loType).toNonRec, f.name)
        }
        fr.copy(fields = newFields)
      }
      case other => other
    }
  }

  def getTypedefs: Block = {
    typeSet.foldLeft(Block(Nop::Nil)) { 
      case (block, td) => block + td
    }
  }

}

/** Replaces each empty `range` value of an array operator with
  * `Some(r)` where `r` spans all ements of the array.
  *
  * This is a prerequisite for the [[ressort.lo.compiler.ArrayStructs]]
  * transformation, as these expressions must be converted to use the resulting
  * `len` fields in the generated structs.
  */
object ExplicitRanges extends TypedLoAstTransform {
  type T = Unit

  def transArrOp(aop: ArrOp): LoAst = {
    val range = aop.opRange
    val arr = aop.opArr
    val newRange = range match {
      case Some(r) => Some(r)
      case None => Some(ArrOpRange(Const(0), NumEntries(arr)))
    }
    val res = aop match {
      case PrefixSum(arr, range) => PrefixSum(arr, newRange)
      case RotLeft(arr, shamt, range) => RotLeft(arr, shamt, newRange)
      case RotRight(arr, shamt, range) => RotRight(arr, shamt, newRange)
      case Reverse(arr, range) => Reverse(arr, newRange)
      case Memset(arr, value, range) => Memset(arr, value, newRange)
    }
    res
  } 

  def trans(oldAst: TypedLoAst, children: List[XFormAst]): XFormAst = {
    val newCh = replaceChildren(oldAst.ast, children)
    val newAst = newCh match {
      case aop: ArrOp => (transArrOp(aop))
      case _ => newCh
    }
    XFormAst(newAst, ())
  }

  def apply(ast: TypedLoAst): TypedLoAst ={
    TypedLoAst(dfTrans(ast).newAst)
  }
}
