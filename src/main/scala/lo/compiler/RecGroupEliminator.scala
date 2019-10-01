// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._
import ressort.util
import scala.collection.mutable.LinkedHashMap


/** Turns all [[SplitRecord]]s into structs of arrays of [[FlatRecord]]s. */
class RecGroupEliminator extends TypedLoAstTransform {

  type T = Unit

  /** Determines the corresponding _new_ type for an array of record groups */
  private object NewTypes {
    private val gArrayTypedefs = LinkedHashMap[SplitRecord, Typedef]()
    private val gArrayStructs = LinkedHashMap[SplitRecord, Struct]()

    def apply(t: SplitRecord): TypeRef = {
      TypeRef(struct(t).name)
    }

    def typedef(t: SplitRecord): Typedef = {
      if (gArrayTypedefs.contains(t)) {
        gArrayTypedefs(t)
      } else {
        val s = makeStruct(t)
        gArrayStructs(t) = s
        val td = Typedef(s)
        gArrayTypedefs(t) = td
        td
      }
    }

    def struct(t: SplitRecord): Struct = {
      if (gArrayStructs.contains(t)) {
        gArrayStructs(t)
      } else {
        val td = typedef(t)
        gArrayStructs(t)
      }
    }

    def allTypedefs = gArrayTypedefs.map(_._2)

    private def makeStruct(r: SplitRecord): Struct = {
      val fields = for ((group, i) <- r.groups.zipWithIndex) yield {
        val fname = nthGroupName(i, group)
        val ftype = Ptr(Arr(FlatRecord(group.fields, Some(fname), r.const)))
        (fname -> ftype)
      }
      Struct(groupStructName(r), fields)
    }
  }

  /** Defines the convention for naming fields of a UGroup's resulting struct */
  private def nthGroupName(n: Int, group: Record.Group): Id = {
    if (group.fields.length == 1 && group.fields.head.name.nonEmpty)
      group.fields.head.name.get
    else
      Id(s"group_$n")
  }

  /** Defines canonical naming for structs generated from `RecGroup`s */
  private def groupStructName(r: SplitRecord): Id = {
    r.name.map(n => Id(s"_${n.name}_gr")).getOrElse(Id(s"_${r.mangledName}_arr"))
  }

  /** For the `n`th field in each record, stores its group, and offset therein */
  private object FieldMaps {
    /** For each record, a (group name, offset) pair for each field */
    private val umaps = LinkedHashMap[SplitRecord, IndexedSeq[(Id, Int)]]()

    /** For each record, a map of named fields to their group names */
    private val nmaps = LinkedHashMap[SplitRecord, Map[Id, Id]]()

    def accessNthField(r: SplitRecord, n: Int): (Id, Int) = {
      if (!umaps.contains(r))
        newFieldMap(r)
      umaps(r)(n)
    }

    def fieldGroupName(r: SplitRecord, field: Id): Id = {
      if (!nmaps.contains(r))
        newFieldMap(r)
      nmaps(r)(field)
    }

    private def newFieldMap(r: SplitRecord): Unit = {
      var umap = Seq[(Id, Int)]()
      var nmap = Map[Id, Id]()
      for ((group, index) <- r.groups.zipWithIndex) {
        for ((field, offset) <- group.fields.zipWithIndex) {
          val groupName = nthGroupName(index, group)
          umap = (groupName, offset) +: umap
          field.name.map(n => nmap += (n -> groupName))
        }
      }
      umaps(r) = umap.toIndexedSeq.reverse
      nmaps(r) = nmap
    }
  }

  /** Performs the actual bulk of the rec group transform by capturing LValues
    * that refer to arrays of record groups, and inverting them.
    */
  private object RecGroupExprTrans extends ExprTransform {
    type T = Unit 
    def trans(
        oldExpr: Expr,
        children: List[XFormExpr],
        scope: Symtab=Symtab.Empty) = {
      val newCh = replaceChildren(oldExpr, children)
      val newExpr = newCh match {
        case UField(Subsc(e, n), origField, origName) => scope(e).loType match {
          case Arr(r: SplitRecord, _) => {
            val (group, newField) = FieldMaps.accessNthField(r, origField)
            val res = UField(Subsc(Deref(Field(e, group)), n), newField, origName)
            res
          }
          case _ => newCh
        }
        case Field(Subsc(e, n), origField) => scope(e).loType match {
          case Arr(r: SplitRecord, _) => {
            val group = FieldMaps.fieldGroupName(r, origField)
            val res = Field(Subsc(Deref(Field(e, group)), n), origField)
            res
          }
          case _ => newCh
        }
        case Size(r: SplitRecord) => Size(transLoType(Record(r.fields:_*)))
        case Size(t) => Size(transLoType(t))
        case NumEntries(a) => scope(a).loType match {
          case Arr(r: SplitRecord, _) => {
            // It doesn't matter which group we use, so use the 0th
            NumEntries(Deref(a.toLValue.dot(nthGroupName(0, r.groups.head))))
          }
          case _ => newCh
        }
        case _ => newCh
      }
      XFormExpr(newExpr, ())
    }
  }
    

  private def transLoType(t: LoType): LoType = t match {
    case Ptr(Arr((r : SplitRecord), c), _) => {
      Ptr(NewTypes.struct(r))
    }
    case r: FlatRecord => {
      val newFields = for (f <- r.fields) yield {
        f.copy(loType = transLoType(f.loType).toNonRec)
      }
      r.copy(fields = newFields)
    }
    case Ptr(t, c) => Ptr(transLoType(t), c)
    case Arr(t, c) => Arr(transLoType(t).toData, c)
    case Struct(name, fields, const) => {
      val newFields = fields map {
        case (f,t) => (f -> transLoType(t).toComplete)
      }
      Struct(name, newFields, const)
    }
    case _ => t
  }

  /** Applies `f` to both sides of an LValue update, and if the type is a pointer to a
    * split record array, instead generates a block of updates for each group's column.
    *
    * @return A pair of the new AST and whether it was modified
    */
  private def applyToAllGroups(lhs: LValue, rhs: Expr, loType: LoType)
                              (f: (LValue, Expr) => LoAst): (LoAst, Boolean) = {
    loType match {
      case Ptr(Arr(r: SplitRecord, _), _) => {
        val td = NewTypes.typedef(r)
        val stmts = for ((groupName, groupType) <- td.fields) yield {
          // In this case, `rhs` must be an `LValue`, since it contained a pointer
          f(Deref(lhs).dot(groupName), Deref(rhs.asInstanceOf[LValue]).dot(groupName))
        }
        (Block(stmts.toList), true)
      }
      case _ => (f(lhs, rhs), false)
    }
  }

  /** Returns code to allocate or free rec-group structs for `Ptr(Arr(SplitRecord(...)))`s
    * inside of structs.
    */
  private def innerStructAllocs(lv: LValue, loType: LoType, free: Boolean=false): LoAst = {
    def allocInner(lv: LValue, loType: LoType, isInner: Boolean=true): LoAst = {
      loType match {
        case Struct(_, fields, _) => {
          val allocs = for ((name, loType) <- fields) yield {
            val deref = if (isInner) lv.dot(name) else lv.dash(name)
            val inner = if (isInner) Nop else allocInner(deref, loType)
            val my = loType match {
              case Ptr(Arr(r: SplitRecord, _), _) => {
                val block = if (free) Free(deref) else HeapAlloc(deref)
                println(block)
                block
              }
              case _ => Nop
            }
            inner + my
          }
          Block(allocs.toList)
        }
        case _ => Nop
      }
    }

    allocInner(lv, loType, false)
  }

  def trans(oldAst: TypedLoAst, children: List[XFormAst]) = {
    val newExprsOp = transExprs(RecGroupExprTrans, oldAst.ast, oldAst.scope)
    val newOldAst = replaceChildren(newExprsOp, children)
    val newAst = newOldAst match {
      case Dec(id, loType) => {
        Dec(id, transLoType(loType))
      }
      case Assign(id, value) => {
        // If a pointer to an array of SplitRecords is assigned, generate
        // assignments for its individual record group arrays instead
        val (block, _) = applyToAllGroups(id, value, oldAst.exprChildren(1).loType) { (lhs, rhs) =>
          Assign(lhs, rhs)
        }
        block
      }
      case DecAssign(id, loType, value) => {
        DecAssign(id, transLoType(loType), value)
      }
      case HeapAlloc(l, Some(length)) => {
        val loType = oldAst.exprChildren.head.loType
        val (block, changed) = applyToAllGroups(l, l, loType) { (lhs, _) => HeapAlloc(lhs, Some(length)) }

        if (changed) HeapAlloc(l) + block else block
      }
      case HeapAlloc(l, None) => HeapAlloc(l) + innerStructAllocs(l, oldAst.exprChildren.head.loType.toPtr.loType)
      case Free(l) => innerStructAllocs(l, oldAst.exprChildren.head.loType.toPtr.loType, free=true) + Free(l)
      case FuncDec(name, params, body, returnType) => {
        val newParams = for ((id, loType) <- params) yield {
          (id -> transLoType(loType).toPrimitive)
        }
        val newReturn = returnType.map(transLoType(_).toPrimitive)
        FuncDec(name, newParams, body, newReturn)
      }
      case Typedef(Struct(name, fields, const)) => {
        val newFields = fields map {
          case (id, loType) => (id -> transLoType(loType).toComplete)
        }
        Typedef(Struct(name, newFields, const))
      }
      case _ => newOldAst
    }
    XFormAst(newAst, ())
  }
}

object RecGroupEliminator  {
  def apply(o: TypedLoAst): TypedLoAst = {
    val rge = new RecGroupEliminator()
    val postMBF = MaterializeByFields(o)
    val code = rge.dfTrans(postMBF).newAst
    val defs = {
      val block = Block(rge.NewTypes.allTypedefs.toList)
      block
    }
    TypedLoAst(defs + code)
  }
}


/** Converts record assignment to field-by-field assignment.
  *
  * Whenever a record group is assigned or passed by value, it is materialized
  * into a flat record type, and built up by assignment to individual fields.
  *
  * @note This is needed as a prerequisite to the `RecGroupElimination` transform,
  *       as records passed by value must be materialized.
  */
class MaterializeByFields extends TypedLoAstTransform {
  type T = Unit

  private val asPrefix = "_rge_"
  private val tmpIds = new TempIds(asPrefix)


  def trans(oldAst: TypedLoAst, children: List[XFormAst]) = {
    val newExprsOp = oldAst.ast
    val newOldAst = replaceChildren(newExprsOp, children)
    val newAst = newOldAst match {
      case Assign(lv, expr) => {
        // In the case of an `Assign`, either _completely replace__ the assign
        // by materializtion assigns, or leave untouched
        materializeAssign(lv, oldAst.scope, expr) getOrElse newOldAst
      }
      case DecAssign(id, loType, value) => {
        val newTexpr = transLoType(loType)
        val assigns = materializeAssign(id, oldAst.scope, value)
        assigns match {
          case Some(block) => {
            Dec(id, newTexpr) + block
          }
          case None => DecAssign(id, newTexpr, value)
        }
      }
      case Dec(id, loType) => {
        Dec(id, transLoType(loType))
      }
      case FuncDec(name, params, body, returnType) => {
        val newParams = params.map { case (id: Id, prim: Primitive) => 
          (id -> transLoType(prim).toPrimitive)
        }
        val newReturn = returnType.map(transLoType).map(_.toPrimitive)
        FuncDec(name, newParams, body, newReturn)
      }
      case App(func, args) => {
        // Arguments that contain scalar groups require materialization, which
        // in turn requires new scalar temporaries be declared and assigned
        // prior to the application.
        val decs = for ((id, expr) <- args) yield {
          oldAst.scope(expr).loType match {
            case r: SplitRecord => {
              val tmp = tmpIds.newId(id.name)
              val newType = transLoType(r).toPrimitive
              Some(Dec(tmp, newType))
            }
            case other => None
          }
        }
        val newArgs = for ((dec, (id, expr)) <- decs zip args) yield {
          (id -> (dec.map(_.sym) getOrElse expr))
        }
        val assigns = (decs zip args) collect { case (Some(dec), (id, expr)) =>
          materializeAssign(dec.sym, oldAst.scope, expr)
        }
        val newApp = App(func, newArgs)
        val newAst: LoAst = assigns.flatten match {
          case Nil => newApp
          case seq => Block(seq.toList) + newApp
        }
        newAst 
      }
      case Typedef(Struct(name, fields, const)) => {
        val newFields = fields map {
          case (id, loType) => (id -> transLoType(loType).toComplete)
        }
        Typedef(Struct(name, newFields, const))
      }
      case other => other
    }
    XFormAst(newAst, ())
  }

  /** Converts a scalar record group type into its flat record form */
  private def transLoType(loType: LoType): LoType = loType match {
    case r: SplitRecord => FlatRecord(name = r.name, fields = r.fields, const = r.const)
    case other => other
  }


  /** Returns materialization assignments for the fields of `[lv] := [expr]`, if any. */
  private def materializeAssign(
      lv:     LValue,
      scope:   Symtab,
      value:  Expr): Option[LoAst] = {
    scope(value).loType match {
      case r: SplitRecord => {
        // Only an LValue expression could produce a record group-typed scalar
        val assigns = for ((f, i) <- r.fields.zipWithIndex) yield {
          f.name match {
            case Some(id) => Field(lv, id) := Field(value.toLValue, id)
            case None => (UField(lv, i) := UField(value.toLValue, i))
          }
        }
        Some(Block(assigns.toList))
      }
      case _ => None
    }
  }
}


object MaterializeByFields {
  def apply(ast: TypedLoAst): TypedLoAst = {
    val mbf = new MaterializeByFields()
    TypedLoAst(mbf.dfTrans(ast).newAst)
  }
}
