package ressort.lo.compiler
import ressort.lo._
import ressort.util
import scala.collection.mutable.LinkedHashMap

/** Turns all [[FlatRecord]]s into structs.
  *
  * Note that this transform assumes [[RecGroupEliminator]] as a prerequisite.
  */
class RecStructs extends TypedLoAstTransform {
  type T = Unit

  private val recMap = LinkedHashMap[FlatRecord, Struct]()

  private object tempIds {
    var counter = 0
    def newId(name: String): Id = {
      val res = s"_rss_$counter"
      counter += 1
      Id(res)
    }
  }

  def trans(oldAst: TypedLoAst, children: List[XFormAst]) = {
    val newExprsOp = transExprs(RecStructsExprs, oldAst.ast, oldAst.scope)
    val newOldAst = replaceChildren(newExprsOp, children)
    val newAst = newOldAst match {
      case Dec(id, loType) => Dec(id, transLoType(loType))
      case DecAssign(id, loType, expr) => DecAssign(id, transLoType(loType), expr)
      case FuncDec(name, params, body, returnType) => {
        val newParams = for ((id, loType) <- params) yield {
          (id -> transLoType(loType).toPrimitive)
        }
        val newReturn = returnType.map(transLoType(_).toPrimitive)
        FuncDec(name, newParams, body, newReturn)
      }
      case Typedef(Struct(name, fields, const)) => {
        val newFields = for ((id, loType) <- fields) yield {
          (id -> transLoType(loType).toComplete)
        }
        Typedef(Struct(name, newFields, const))
      }
      case _ => newOldAst
    }
    XFormAst(newAst, ())
  }

  /** Returns block of [[ressort.lo.Typedef]]s for each new struct made by
    * this transform.
    */
  def getTypedefs: List[Typedef] = {
    var list = List[Typedef]()
    for ((rec, struct) <- recMap) {
      list :+= Typedef(struct)
    }
    list
  }


  private def transLoType(t: LoType): LoType = {
    t match {
      case s: SplitRecord => {
        throw new AssertionError(
          s"Error: should have removed split record $s in RecGroupEliminator transform.")
      }
      case f: FlatRecord => transFlatRecord(f)
      case Ptr(t2, const) => Ptr(transLoType(t2), const)
      case Arr(t2, const) => Arr(transLoType(t2).toData, const)
      case Struct(name, fields, const) => {
        Struct(
          name,
          fields.map(f => f._1 -> transLoType(f._2).toComplete),
          const)
      }
      case _ => t
    }
  }

  private def transFlatRecord(rec: FlatRecord): Scalar = {
    if(recMap.contains(rec))
      return recMap(rec)

    if (rec.fields.length == 1) {
      val loType = rec.fields.head.loType
      return loType
    }

    val fieldTypes = {
      val fieldNames: Seq[(Id, Complete)] = {
        for ((field, num) <- rec.fields.zipWithIndex) yield {
          field.name.getOrElse(nthFieldName(num)) -> transLoType(field.loType).toComplete
        }
      }
      fieldNames
    }
   
    val name = rec.name match {
      case Some(id) => id.name
      case None => {
        // Give structs a type name that reflects the types of all the
        // individual fields
        val typeNameStr = fieldTypes.foldLeft("") {
          case (str, (_, loType)) => str + loType.mangledName + "_"
        }

        // We need to mangle typeNameStr to remove spaces that result from, for 
        // instance, const qualifiers.
        val mangledTypeNameStr = typeNameStr.replaceAll(" ", "_")
        "Rec_"+mangledTypeNameStr.take(10)
      }
    }
    val struct = Struct(tempIds.newId(name), fieldTypes)
    recMap += (rec -> struct)
    struct
  }
  
  private def nthFieldName(n: Int): Id = {
    Id("field"+n)
  }

  private object RecStructsExprs extends ExprTransform {
    type T = Unit

    def trans(
        oldExpr: Expr,
        children: List[XFormExpr],
        scope: Symtab=Symtab.Empty) = {
      val newCh = replaceChildren(oldExpr, children)
      val newExpr = newCh match {
        case UField(ur, fieldNum, _) => {
          val recType = scope(ur).loType.toRecord
          if (recType.fields.length == 1) {
            children.head.newExpr
          } else {
            val field = recType.fields(fieldNum)
            val fieldName = field.name.getOrElse(nthFieldName(fieldNum))
            Field(children.head.newExpr.toLValue, fieldName)
          }
        }
        case Field(nr, _) => {
          val recType = scope(nr).loType
          recType match {
            case FlatRecord(Seq(f), _, _) => children.head.newExpr
            case _ => newCh
          }
        }
        case Size(t) => Size(transLoType(t))
        // Named fields already use Field() specifiers
        case _ => newCh
      }
      XFormExpr(newExpr, ())
    }
  }
}

object RecStructs  {
  def apply(ast: TypedLoAst): TypedLoAst = {
    val rs = new RecStructs()
    val newAst = rs.dfTrans(ast).newAst
    val typedefs = Block(rs.getTypedefs)
    TypedLoAst(typedefs + newAst)
  }
}
