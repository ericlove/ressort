// See LICENSE.txt
package ressort.lo;
import ressort.util._
import scala.collection.mutable.HashMap
import ressort.hi
import ressort.lo.interp.EAddr

import ExprChecker._



/** All type checking will return either a typed expression (TypedExpr) or
  * an ExprTypeErr when the expression is malformed.
  *
  * In both cases, scope is the scope in which the checking was perormed.
  * In the case of an error, an optional string may be supplied in err
  * to indicate the nature of the error.
  *
  * The mutable state described below (`scopedSym` and `eaddr`) enable performance optimizations.
  *
  * @param scopedSym A globally scoped and unique version of a [[SymLike]] in `expr`
  * @param eaddr An address of this (l-valuable) expression in the interpreter.
  */
class TypedExpr(
    var expr: Expr,
    var loType: LoType,
    var scope: Symtab,
    var children: List[TypedExpr]=Nil,
    var lines: Option[LoAstLines]=None,
    var scopedSym: Option[ScopedSym]=None,
    var eaddr: Option[EAddr]=None)

case class ExprTypeErr(expr: Expr, scope: Symtab, err: String)

class ExprChecker(scope: Symtab) {
  implicit def checkerResult(ec: ExprNodeChecker): ECheckRes = ec.check

  private def typeOf(e: Expr, lines: Option[LoAstLines]): ECheckRes = e match {
    case Const(n) => {
      if(n<0) { 
        Right(new TypedExpr(e, UInt64(const=true), scope, Nil, lines))
      } else { 
        Right(new TypedExpr(e, Index(const=true), scope, Nil, lines))
      }
    }
    case FloatConst(f) => Right(new TypedExpr(e, LoFloat(const=true), scope, Nil, lines))
    case DoubleConst(f) => Right(new TypedExpr(e, LoDouble(const=true), scope, Nil, lines))
    case True => Right(new TypedExpr(e, Bool(const=true), scope, Nil, lines))
    case False => Right(new TypedExpr(e, Bool(const=true), scope, Nil, lines))
    case Null => Right(new TypedExpr(e, NullType, scope, Nil, lines))
    case c @ Cast(e, t) => CheckCast(c, scope, lines)
    case p @ Plus(e1, e2) => CheckPrimitiveOp("+", p, scope, lines)
    case m @ Minus(e1, e2) => CheckPrimitiveOp("-", m, scope, lines)
    case d @ Div(e1, e2) => CheckPrimitiveOp("/", d, scope, lines)
    case m @ Mul(e1, e2) => CheckPrimitiveOp("*", m, scope, lines)
    case n @ Neg(e1) => CheckPrimitiveOp("!", n, scope, lines)
    case p @ Pow(e1, e2) => CheckPrimitiveOp("Pow()", p, scope, lines)
    case p @ Pow2(exp) => CheckPrimitiveOp("Pow2()", p, scope, lines)
    case m @ Mod(e1, e2) => CheckPrimitiveOp("Mod()", m, scope, lines)
    case f @ FakeUse(e) => CheckAny(f, scope, lines)
    case s @ Safe(e) => CheckAny(s, scope, lines)
    case m @ MarkedExpr(_, _) => CheckAny(m, scope, lines)
    case v: SymLike => {
      lazy val errMsg = {
        s"Identifier $v undefined in current scope.\n"
      }
      scope.symType(v) match {
        case Some(loType) => Right(new TypedExpr(v, loType, scope, Nil, lines, Some(scope.unique(v))))
        case None => Left(ExprTypeErr(v, scope, errMsg) :: Nil)
      }
    }
    case lt @ Less(e1, e2) => CheckComparison("<", lt, scope, lines)
    case gt @ Greater(e1, e2) => CheckComparison(">", gt, scope, lines)
    case ge @ GreaterEq(e1, e2) => CheckComparison(">=", ge, scope, lines)
    case le @ LessEq(e1, e2) => CheckComparison("<=", le, scope, lines)
    case sl @ ShiftLeft(e1, e2) => CheckShift(sl, scope, lines)
    case sr @ ShiftRight(e1, e2) => CheckShift(sr, scope, lines)
    case ba @ BitAnd(e1, e2) => CheckBitAnd(ba, scope, lines)
    case s @ Subsc(e1, e2) => CheckSubsc(s, scope, lines)
    case d @ Deref(e) => CheckDeref(d, scope, lines)
    case r @ Ref(e) => CheckRef(r, scope, lines)
    case f @ Field(struct, field) => CheckField(f, scope, lines)
    case eq @ Equal(e1, e2) => CheckComparison("==", eq, scope, lines)
    case a @ And(e1, e2) => CheckLogicalOp(a, scope, lines)
    case o @ Or(e1, e2) => CheckLogicalOp(o, scope, lines)
    case n @ Not(e) => CheckLogicalOp(n, scope, lines)
    case m @ Mux(cond, e1, e2) => CheckMux(m, scope, lines)
    case p @ Phi(cond, e1, e2) => CheckMux(Mux(cond, e1, e2), scope, lines)
    case uf @ UField(lv, n, _) => CheckUField(uf, scope, lines)
    case r @ BitRange(_,_,_) => CheckRange(r, scope, lines)
    case lvr @ LVRange(_,_,_) => CheckRange(lvr, scope, lines)
    case s @ Size(_) => CheckSize(s, scope, lines)
    case ne @ NumEntries(_) => CheckNumEntries(ne, scope, lines)
    case lw @ LowerWord(_) => CheckLowerWord(lw, scope, lines)
    case l2u @ Log2Up(e) => CheckLog2Up(l2u, scope, lines)
    case esc @ Escape(e, from, to, f) => CheckEscape(esc, scope, lines)
  }

  def apply(e: Expr, lines: Option[LoAstLines]=None): ECheckRes = typeOf(e, lines)
}

object ExprChecker {
  /** Returned by all code that type-checks expressions:
  * 
  * Right projection used on success -- a typed expression
  * Left projection used on failure -- a list of expression
  * typing errors returned by checking of sub expressions.
  */
  type ECheckRes = Either[List[ExprTypeErr], TypedExpr]
}



/** Provides type-checking for a class of expressions.
  *
  * Implementations must specify constraints on types
  * that sub-expressions may take.
  */
abstract trait ExprNodeChecker {
  /** Determine if types of sub-expressions are valid.
    *
    * Returns Nil if specific combination of sub-expression types is
    * allowed by this kind of expression;
    * returns a list ExprTypeErr values if this is not the case
    */
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr]

  /** Returns the resulting LoType of this expression, given the types
    * of all sub-expressions.
    */
  def resultType(childTypes: List[LoType]): LoType

  val scope: Symtab
  val expr: Expr
  val lines: Option[LoAstLines]


  /** Type-checks an expression.
    *
    * Returns an ECheckRes with the appropriate TypedExpr on success,
    * or returns an ExprTypeErr with the relevant message, or those
    * of sub-expressions type errors, on failure.
    */
  def check: ECheckRes = {
    val childCheckRes = expr.children.map(scope.exprChecker(_, lines))

    val childErrs = childCheckRes.flatMap(_.left.toOption getOrElse Nil)

    // Produce a list of types of all sub-expressions, replacing those that
    // failed type checking by NoType in order to allow checking to continue.
    val childTypes = {
      for {
        res <- childCheckRes 
      } yield res match {
        case Right(texpr) => texpr.loType
        case _ => NoType
      }
    }
    assert(childTypes.length == expr.children.length)

    // Don't report any invalid type errors if any child expr has type NoType,
    // since this means an error was already detected, and we want to avoid an 
    // explosion of spurious type errors from comparison against NoType.
    val disallowedErrs = if (childTypes.contains(NoType)) {
      Nil
    } else {
      childTypesValid(childTypes) 
    }

    val errs = childErrs ++ disallowedErrs
    if(errs isEmpty)
      Right(new TypedExpr(expr, resultType(childTypes), scope, childCheckRes.map(_.right.get), lines))
    else
      Left(errs)
  }
}



/** Type-checks an expression whose sub-expressions must all be of equivalent
  * types, as defined by the isValidType() predicate.
  *
  * Derived classes must define the isValidType function to select the range
  * of LoTypes for which this expression is valid.
  * They must also define the symbol string to produce a graphical
  * representation of this operator in error messages, and also must 
  * determine the result type.
  */
abstract class EquivTypeExprChecker extends ExprNodeChecker {
  val expr: Expr
  val scope: Symtab
  val symbol: String          // Symbol used to represent this operator

  def isValidType(t: LoType): Boolean

  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val childTypeErrs = expr.children zip childTypes collect {
      case (e, t) if (!isValidType(t)) => {
        val errMsg = {
          s"Operator $symbol not valid "+
          s"for expression [$e] of type $t.\n"
        }
        ExprTypeErr(e, scope, errMsg)
      }
    }

    val typeMismatchErr = {
      if (!childTypes.exists(t => childTypes.forall(t.nonConst.accepts(_)))) {
        val errMsg = s">>> $expr : cannot combine types ${childTypes.mkString(",")}"
        List(ExprTypeErr(expr, scope, errMsg))
      } else {
        Nil
      }
    }

    typeMismatchErr ++ childTypeErrs
  }
}

case class CheckPrimitiveOp(
    symbol: String,
    expr: Expr,
    scope: Symtab,
    lines: Option[LoAstLines]) extends EquivTypeExprChecker {
  def isValidType(t: LoType): Boolean = t.isInstanceOf[Primitive]
  def resultType(childTypes: List[LoType]): LoType = {
    for (t <- childTypes) {
      if (childTypes.forall(t.nonConst.accepts(_)))
        return t.nonConst
    }
    throw new Error(s">>> $expr : cannot combine types $childTypes")
  }
}

case class CheckComparison(
    symbol: String,
    expr: Expr,
    scope: Symtab,
    lines: Option[LoAstLines]) extends EquivTypeExprChecker {
  def isValidType(t: LoType): Boolean = t.isInstanceOf[Primitive]
  def resultType(childTypes: List[LoType]): LoType = Bool()
}

   

case class CheckSubsc(
    expr: Subsc,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val lvType = childTypes(0)
    val nType = childTypes(1)

    val containerErr: List[ExprTypeErr] = lvType match {
      case c: Arr => Nil
      case other => {
        val errMsg = {
          s"LValue [${expr.l}] of non-container type $other "+
          s"used in subscript.\n"
        }
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
    }

    val nonIntIndexErr: List[ExprTypeErr] = nType match {
      case iv: IntValued => Nil
      case other => {
        val errMsg = {
          s"Expression [${expr.n}] of non-integer type $nType "+
          s"used as subscript index."
        }
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
    }

    containerErr ++ nonIntIndexErr
  }

  def resultType(childTypes: List[LoType]): LoType = {
    val lvType = childTypes(0)
    lvType match {
      case a: Arr => a.elementType.setConst(a.const)
      case other => NoType
    }
  }
}
case class CheckShift(
    expr: Shift,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val eType = childTypes(0)
    val shamtType = childTypes(1)

    val nonRecErr: List[ExprTypeErr] = eType match {
      case n: NonRec => Nil
      case other => {
        val errMsg = {
          s"Expression [${expr.e1}] of non-primitive type $eType used in shift.\n"
        }
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
    }

    val nonIntShamtErr: List[ExprTypeErr] = shamtType match {
      case iv: IntValued => Nil
      case other => {
        val errMsg = {
          s"Expression [${expr.e2}] of non-integer type $shamtType "+
              s"used as shift amount.\n"
        }
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
    }

    nonRecErr ++ nonIntShamtErr
  }

  def resultType(childTypes: List[LoType]): LoType = {
    childTypes(0)
  }
}
case class CheckBitAnd(
    expr: BitAnd,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val e1Type = childTypes(0)
    val e2Type = childTypes(1)

    def nonRecErr(e: Expr, eType: LoType): List[ExprTypeErr] = eType match {
      case n: NonRec => Nil
      case other => {
        val errMsg = {
          s"Expression [${e}] of non-primitive type $eType used in shift.\n"
        }
        ExprTypeErr(e, scope, errMsg) :: Nil
      }
    }

    nonRecErr(expr.children(0), e1Type) ++ nonRecErr(expr.children(1), e2Type)
  }

  def resultType(childTypes: List[LoType]): LoType = {
    childTypes(0)
  }
}
case class CheckDeref(
    expr: Deref,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val lvType = childTypes(0)
    lvType match {
      case Ptr(loType, _) => Nil
      case other => {
        val errMsg = {
          s"Dereferencing expression [${expr.l}] "+
          s"of non-pointer type $lvType.\n"
        }
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
    }
  }

  def resultType(childTypes: List[LoType]): LoType = {
    val lvType = childTypes(0)
    lvType match { 
      case Ptr(loType, _) => loType
      case _ => NoType
    }
  }
}

case class CheckField(
    expr: Field,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {

  def resultOrErr(lvType: LoType): Either[LoType, ExprTypeErr] = {
    val fieldName = expr.field
    val lv = expr.lv
    lazy val noFieldErr = s"Struct/Rec type\n ${indent(lvType.toString)} :\ncontains no field $fieldName.\n"
    lazy val nonRecErr = {
      s"Attempting to extract field ${fieldName} "+
          s"from LValue [${lv}] of non-struct or record type $lvType.\n"
    }
    // Use linear search here because the number of fields is usually small
    // and building a hash map is very expensive.
    def fromStruct(s: Struct): Either[LoType, ExprTypeErr] = {
      for ((name, loType) <- s.fields) {
        if (name == fieldName)
          return Left(loType)
      }
      Right(ExprTypeErr(expr, scope, noFieldErr + s": ${s.fieldMap}"))
    }
    lvType match {
      case tr: TypeRef => {
        val s = scope(tr.name).loType.toStruct
        fromStruct(s)
      }
      case s: Struct => fromStruct(s)
      case rec: Record => {
        for (f <- rec.fields) {
          if (f.name.map(_ == fieldName).getOrElse(false))
            return Left(f.loType)
        }
        Right(ExprTypeErr(expr, scope, noFieldErr))
      }
      case _ => Right(ExprTypeErr(expr, scope, nonRecErr))
    }
  }

  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val lvType = childTypes(0)
    val ftype = resultOrErr(lvType)
    ftype match {
      case Left(ftype) => Nil
      case Right(err) => List(err)
    }
  }


  def resultType(childTypes: List[LoType]): LoType = {
    val lvType = childTypes(0)
    resultOrErr(lvType) match {
      case Left(ftype) => ftype
      case _ => NoType
    }
  }

}

case class CheckLogicalOp(
    expr: Expr,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    def checkType(e: Expr, t: LoType): Option[ExprTypeErr] = t match {
      case Bool(c) => None
      case other => {
        val errMsg = {
          s"Expression [$e] of type $t not valid for logical operator"
        }
        Some(ExprTypeErr(expr, scope, errMsg))
      }
    }

    // Make sure all sub-expressions have a type that's valid either for
    // boolean or bitwise logic.
    val invalidTypeErrs = (expr.children zip childTypes) map { 
      case (e,t) => checkType(e,t) 
    }

    // Make sure all sub-expressions have the *same* valid subtype
    val typeMismatchErrs = for {
      et1 <- (expr.children zip childTypes)
      et2 <- (expr.children zip childTypes)
    } yield {
      if (!et1._2.nonConst.accepts(et2._2)) {
        val errMsg = {
          s"Expressions [${et1._1}] of type ${et1._2} and "+
          s"[${et2._1}] of type ${et2._2} have incompatible types."
        }
        Some(ExprTypeErr(expr, scope, errMsg))
      } else {
        None
      }
    }

    invalidTypeErrs.flatten ++ typeMismatchErrs.flatten
  }

  def resultType(childTypes: List[LoType]) = childTypes.head
}


case class CheckMux(
    expr: Mux,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]) = {
    val condType = childTypes(0)
    val e1Type = childTypes(1)
    val e2Type = childTypes(2)

    val condErrs = if (!Bool().accepts(condType)) {
      val errMsg = s"Condition [${expr.cond}] of non-bool type $condType.\n"
      ExprTypeErr(expr, scope, errMsg) :: Nil
    } else {
      Nil
    }

    val mismatchErrs = if (!e1Type.nonConst.accepts(e2Type)) {
      val errMsg = {
        s"Expr [${expr.e1}] of type $e1Type and "+
        s"[${expr.e2}] of type $e2Type have incompaitble types.\n"
      }
      ExprTypeErr(expr, scope, errMsg) :: Nil
    } else {
      Nil
    }

    condErrs ++ mismatchErrs
  }

  def resultType(childTypes: List[LoType]) = {
    val e1Type = childTypes(1)
    e1Type
  }
}


case class CheckRef(
    expr: Ref,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    childTypes(0) match {
      case r: SplitRecord => {
        val errMsg = s"Must not take reference of scalar SplitRecord in $expr"
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
      case loType => Nil
    }
  }

  def resultType(childTypes: List[LoType]): LoType = Ptr(childTypes(0))
}


case class CheckUField(
    expr: UField,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val lvType = childTypes(0)

    lvType match {
      case rec: Record => Nil
      case s: Struct => Nil
      case t: TypeRef => Nil
      case _ => {
        val errMsg = s"LValue ${expr.lv} is of non-struct or record type $lvType.\n"
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
    }
  }

  def resultType(childTypes: List[LoType]): LoType = {
    val lvType = childTypes(0)
    lvType match {
      case rec: Record => rec.fields(expr.field).loType
      case s: Struct => s.fields(expr.field)._2
      case t: TypeRef => scope(t.name).loType.toStruct.fields(expr.field)._2
      case _ => ??? // Can't happen due to initial match
    }
  }
}

case class CheckRange(
    expr: Expr, // Could be Range or LVRange
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  // Since expr could be a Range or LVRange, we consider the "head"
  // of the expression to be the sub-expression to which the range
  // operator is applied (i.e. Range(e, start, end) has head e).

  // Determine the result type of the Range() expression, or
  // return None if the head expr is not of a Range()-able type.
  def rangeType(headType: LoType): Option[LoType] = headType match {
    case Arr(t, _) => Some(Arr(t))
    case iv: IntValued => Some(iv)
    case _ => None
  }

  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val head = expr.children.head
    val headType = childTypes(0)
    val resultTypeRes = rangeType(headType)
    
    val rangeExprs = expr.children.tail // [start, end]
    val rangeExprTypes = childTypes.tail 

    val headTypeErr = resultTypeRes match {
      case Some(t) => Nil
      case None => {
        val errMsg = { 
          s"Expr [${head}] of type $headType not valid for Range()."
        }
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
    }

    val rangeExprErrs = (rangeExprs zip rangeExprTypes) collect {
      case (e, other) if (!other.isInstanceOf[IntValued]) => {
        val errMsg = {
          s"Expression [$e] of non-int-valued type $other "+
          s"used in start or end of Range() expression.\n"
        }
        ExprTypeErr(expr, scope, errMsg)
      }
    }

    headTypeErr ++ rangeExprErrs
  }

  def resultType(childTypes: List[LoType]): LoType = {
    val headType = childTypes(0)
    rangeType(headType).get
  }
}

case class CheckAny(
    expr: Expr,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = Nil
  def resultType(childTypes: List[LoType]): LoType = childTypes.head
}

case class CheckSize(
    expr: Size,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = Nil
  def resultType(childTypes: List[LoType]): LoType = Index()
}

case class CheckNumEntries(
    expr: NumEntries,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val eType = childTypes(0)
    eType match {
      case c: Arr => Nil
      case other => {
        val errMsg = {
          s"Cannot take NumEntries() of expression ${expr.e} "+
          s"with non-container type $eType.\n"
        }
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
    }
  }

  def resultType(childTypes: List[LoType]): LoType = Index()
}

case class CheckLowerWord(
    expr: LowerWord,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val eType = childTypes(0)
    eType match {
      case iv: IntValued => Nil
      case Bits(_) => Nil
      case other => {
        val errMsg = { 
          s"Cannot extract lower word from expression [${expr.e}] " +
          s"of type $eType.\n"
        }
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
    }
  }

  def resultType(childTypes: List[LoType]): LoType = UInt()
}

case class CheckLog2Up(
    expr: Log2Up,
    scope: Symtab,
    lines: Option[LoAstLines]) extends ExprNodeChecker {
  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val eType = childTypes(0)
    eType match {
      case iv: IntValued => Nil
      case _ => {
        val errMsg = {
          s"Expression [${expr.e}] of non-int type $eType "+
          s"used in Log2Up() expression.\n"
        }
        ExprTypeErr(expr, scope, errMsg) :: Nil
      }
    }
  }

  def resultType(childTypes: List[LoType]): LoType = Index()
}


case class CheckCast(
    expr: Cast,
    scope: Symtab,
    lines: Option[LoAstLines])
  extends ExprNodeChecker {

  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val eType = childTypes.head

    // Handle cases where explicit conversion is not otherwise covered by `accepts()` coercion
    (expr.t, eType) match {
      case (to, from) if to.accepts(from) => Nil
      case (b: Bool, n: NonRec) => Nil
      case (f: LoFloat, d: LoDouble) => Nil
      case (iv: IntValued, f: LoFloat) => Nil
      case (iv: IntValued, d: LoDouble) => Nil
      case (iv: IntValued, iv2: IntValued) => Nil
      case _ =>
        val errMsg = s"Cannot cast expression $expr of type $eType to type ${expr.t}"
        ExprTypeErr(expr, scope, errMsg) :: Nil
    }
  }

  def resultType(childTypes: List[LoType]): LoType = expr.t
}

case class CheckEscape(
    expr: Escape,
    scope: Symtab,
    lines: Option[LoAstLines])
  extends ExprNodeChecker {

  def childTypesValid(childTypes: List[LoType]): List[ExprTypeErr] = {
    val eType = childTypes.head
    if (expr.from.accepts(eType)) {
      Nil
    } else {
      val errMsg = s"Escaped expression ${expr.e} has type $eType, but ${expr.from} required"
      ExprTypeErr(expr, scope, errMsg) :: Nil
    }
  }

  def resultType(childTypes: List[LoType]): LoType = expr.to
}
