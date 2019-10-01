// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._
import ressort.util
import scala.collection.mutable.{LinkedHashMap, HashSet}


/** Splits scalar struct definitions into multiple scalar primitives.
  *
  * This is an important optimization to perform prior to dead code elimination,
  * as it will result in the removal of unnecessary loads of unused fields during
  * array scans.
  */
class UnpackScalarStructs(ast: TypedLoAst) extends TypedLoAstTransform {

  type T = Unit

  private val tempIds = new TempIds("_uss_")

  private val referencedIds: Set[ScopedSym] = {
    val rs = new ReferencedScalars()
    rs.dfTrans(ast)
    rs.getSet
  }

  def trans(oldAst: TypedLoAst, children: List[XFormAst]) = {
    val newOldAst0 = replaceChildren(oldAst.ast, children)
    val newOldAst = transExprs(UnpackExprs, newOldAst0, oldAst.scope)
    val newAst = newOldAst match {
      case DecAssign(id, s: Struct, expr) => {
        assert(
          false,
          s"Unexpected DecAssign of scalar struct type $newOldAst; \n" +
          s"should have been eliminated by ScalarFieldAssigns transform.")
        ???
      }
      case Dec(id, s: Struct) => {
        val decs = remapStructDec(ScopedSym(id, oldAst.scope), s)
        Block(decs)
      }
      case other => other
    }
    XFormAst(newAst, ())
  }

  private val remappedLValues = LinkedHashMap[ScopedSym, Map[LValue, SymLike]]()

  private def remapStructDec(scoped: ScopedSym, struct: Struct): List[Dec] = {
    if (referencedIds.contains(scoped)) {
      // Must not remap any scalars that get referenced
      return List(Dec(scoped.sym, struct))
    }

    var fieldDecs = List[Dec]()
    def walk(struct: Struct, path: List[Id]) {
      val prefix = path.foldLeft(scoped.sym.name) { case (p, f) => p + "_" + f.name }
      val lval = path.foldLeft[LValue](scoped.sym) { case (l, f) => l.dot(f) }
      for ((field, baseType) <- struct.fields) {
        baseType match {
          case s: Struct => {
            walk(s, path :+ field)
          }
          case _ => {
            val name = tempIds.newId(prefix + "_" + field.name)
            val init = remappedLValues.getOrElse(scoped, Map[LValue, SymLike]())
            remappedLValues(scoped) = init ++ Map(lval.dot(field) -> name)
            fieldDecs +:= Dec(name, baseType)
          }
        }
      }
    }
    walk(struct, Nil)
    fieldDecs
  }

  private object UnpackExprs extends ExprTransform {
    type T = Unit
    def trans(
        oldExpr: Expr,
        children: List[XFormExpr],
        scope: Symtab=Symtab.Empty) = {
      val newCh = replaceChildren(oldExpr, children)
      // Unlike most transforms, this one matches on the __old__ version
      // of the expression, in order to replace the __larges__ possibe LValue;
      // only if no change is made are children replaced at a given level.
      val newExpr = oldExpr match {
        case lv: LValue if (scope.symType(lv.root).nonEmpty) => {
          val scoped = ScopedSym(lv.root, scope.getEnclosing(lv.root))
          if (remappedLValues.contains(scoped)) {
            remappedLValues(scoped).getOrElse(lv, lv)
          } else {
            newCh
          }
        }
        case _ => {
          newCh
        }
      }
      XFormExpr(newExpr, ())
    }
  }
}

/** Produces a [[scala.collection.Set]] of [[ScopedSym]]s that correspond to scalar
  * values of which a reference is at some point taken.
  */
class ReferencedScalars extends TypedLoAstTransform {
  type T = Unit

  private val referenced = HashSet[ScopedSym]()

  def trans(oldAst: TypedLoAst, children: List[XFormAst]) = {
    transExprs(ExamineExprs, oldAst.ast, oldAst.scope)
    XFormAst(oldAst.ast, ())
  }

  def getSet: Set[ScopedSym] = referenced.toSet

  private object ExamineExprs extends ExprTransform {
    type T = Unit
    def trans(
        oldExpr: Expr,
        children: List[XFormExpr],
        scope: Symtab=Symtab.Empty) = {
      oldExpr match {
        case Ref(l) => {
          val scoped = ScopedSym(l.root, scope.getEnclosing(l.root))
          referenced += scoped
        }
        case _ =>
      }
      XFormExpr(oldExpr, ())
    }
  }
}
  

object UnpackScalarStructs {
  def apply(ast: TypedLoAst): TypedLoAst = {
    val postSsa = ScalarStructAssigns(ast)
    val uss = new UnpackScalarStructs(postSsa)
    val newAst = uss.dfTrans(postSsa).newAst
    TypedLoAst(newAst)
  }
}


/** Turns assignments to scalar structs into field-by-field assignment */
class ScalarStructAssigns(ast: TypedLoAst) extends TypedLoAstTransform {
  type T = Unit

  def trans(oldAst: TypedLoAst, children: List[XFormAst]) = {
    val newOldAst = replaceChildren(oldAst.ast, children)
    val newAst = newOldAst match {
      case Assign(lv, e) => {
        oldAst.scope(lv).loType match {
          case s: Struct => {
            e match {
              case rhs: LValue => assignToStruct(lv, rhs, s)
              case _ => ??? // Will never happen, b/c can't use a Struct in an expr
            }
          }
          case _ => newOldAst
        }
      }
      case DecAssign(id, loType, e) => {
        loType match {
          case s: Struct => Dec(id, loType) + assignToStruct(id, e.toLValue, s)
          case _ => newOldAst
        }
      }
      case other => other
    }
    XFormAst(newAst, ())
  }

  private def assignToStruct(lhs: LValue, rhs: LValue, struct: Struct): LoAst = {
    var assigns = Seq[Assign]()
    def walk(struct: Struct, path: List[Id]) {
      val lhsLv = path.foldLeft[LValue](lhs) { case (l, f) => l.dot(f) }
      val rhsLv = path.foldLeft[LValue](rhs) { case (l, f) => l.dot(f) }
      for ((field, baseType) <- struct.fields) {
        baseType match {
          case s: Struct => {
            walk(s, path :+ field)
          }
          case _ => {
            assigns +:= Assign(lhsLv.dot(field), rhsLv.dot(field))
          }
        }
      }
    }
    walk(struct, Nil)
    Block(assigns.toList)
  }
}

object ScalarStructAssigns {
  def apply(ast: TypedLoAst): TypedLoAst = {
    val ssa = new ScalarStructAssigns(ast)
    val newAst = ssa.dfTrans(ast).newAst
    TypedLoAst(newAst)
  }
}
