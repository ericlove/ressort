// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._
import scala.collection.mutable.HashMap

private class PropagateConstants(typed: TypedLoAst, replaceInsidePhi: Boolean) {
  val knownValues = HashMap[LoSym, ConstExpr]()
  var trueExprs = Set[Expr]()
  var falseExprs = Set[Expr]()

  def rename(e: Expr): Expr = {
    val newCh = e.replaceChildren(e.children.map(rename))
    newCh match {
      case e if trueExprs.contains(e) => True
      case e if falseExprs.contains(e) => False
      case l: LoSym => knownValues.getOrElse(l, l)
      case Plus(c1: ConstExpr, c2: ConstExpr) => c1+c2
      case Plus(e, Const(0)) => e
      case Plus(Const(0), e) => e
      case Minus(c1: ConstExpr, c2: ConstExpr) => c1-c2
      case Minus(e, Const(0)) => e
      case Mul(c1: ConstExpr, c2: ConstExpr) => c1*c2
      case Mul(e, Const(1)) => e
      case Mul(Const(1), e) => e
      case Mul(Const(0), e) => Const(0)
      case Mul(e, Const(0)) => Const(0)
      case Neg(Const(n)) => Const(-n)
      case Div(c1: ConstExpr, c2: ConstExpr) => c1/c2
      case Div(e, Const(1)) => e
      case Mod(Const(c1), Const(c2)) => Const(c1%c2)
      case Pow2(Const(c)) => Const(1L << c)
      case Log2Up(Const(c)) => Const(math.ceil(math.log(c)/math.log(2.0)).toInt)

      case Plus(Plus(e1, c1: ConstExpr), c2: ConstExpr) => Plus(e1, c2 + c1)
      case Plus(Minus(e1, c1: ConstExpr), c2: ConstExpr) => Plus(e1, c2 - c1)
      case Minus(Plus(e1, c1: ConstExpr), c2: ConstExpr) => Plus(e1, c1 - c2)
      case Plus(e1, Neg(e2)) if e1 == e2 => Const(0)

      case Plus(Minus(e1, e2), e3) if (e3 == e2) => e1
      case Minus(Plus(e1, e2), e3) if (e3 == e2) => e1
      case Div(Mul(e1, e2), e3) if (e3 == e2) => e1

      case Equal(c1: ConstExpr, c2: ConstExpr) => if (c1 == c2) True else False
      case Greater(c1: ConstExpr, c2: ConstExpr) => c1 > c2
      case GreaterEq(c1: ConstExpr, c2: ConstExpr) => c1 >= c2
      case Less(c1: ConstExpr, c2: ConstExpr) => c1 < c2
      case LessEq(c1: ConstExpr, c2: ConstExpr) => c1 <= c2

      case And(b1: BoolConst, b2: BoolConst) => b1 && b2
      case And(False, _) => False
      case And(_, False) => False
      case And(True, b2) => b2
      case And(b1, True) => b1
      case Or(b1: BoolConst, b2: BoolConst) => b1 || b2
      case Or(True, _) => True
      case Or(_, True) => True
      case Or(b1, False) => b1
      case Or(False, b2) => b2
      case Not(b: BoolConst) => if (b.value) False else True
      case Mux(b: BoolConst, e1, e2) => if (b.value) e1 else e2
      case Mux(_, e1, e2) if (e1 == e2) => e1
      case ShiftLeft(e1, Const(0)) => e1
      case ShiftRight(e1, Const(0)) => e1
      case BitAnd(e1, Const(0)) => Const(0)
      case ShiftLeft(c1: ConstExpr, c2: ConstExpr) => (c1 << c2)
      case ShiftRight(c1: ConstExpr, c2: ConstExpr) => (c1 >> c2)
      case BitAnd(c1: Const, c2: Const) => (c1 & c2)
      case Safe(c: ConstExpr) => c
      case FakeUse(b: BoolConst) => b
      case FakeUse(c: ConstExpr) => c
      case _ => newCh
    }
  }

  def rename(typed: TypedLoAst): LoAst = {
    val newCh = typed.ast match {
      case IfElse(cond, o1, o2) => {
        trueExprs += cond
        val newO1 = rename(typed.children(0))
        trueExprs -= cond
        falseExprs += cond
        val newO2 = rename(typed.children(1))
        falseExprs -= cond
        List(newO1, newO2)
      }
      case _ => typed.children.map(rename)
    }
    val withNewCh = typed.ast.replaceAstChildren(newCh)
    val newExprs = withNewCh.exprChildren.map(rename)
    val withNewExprs = withNewCh match {
      case Assign(l: LoSym, e) => Assign(typed.ast.exprChildren(0).toLValue, newExprs(1))
      case _ =>
        withNewCh.replaceExprChildren(newExprs)
    }

    withNewExprs match {
      case Assign(l: LoSym, p: Phi) if !replaceInsidePhi => {
        val old = typed.ast.exprChildren(1).children
        val res = Assign(typed.ast.exprChildren(0).toLValue, Phi(newExprs(1).children.head, old(1), old(2)))
        res
      }
      case Assign(l: LoSym, c: ConstExpr) => {
        knownValues(l) = c
        withNewExprs
      }
      case Assign(l: LoSym, Safe(c: ConstExpr)) => {
        knownValues(l) = c
        withNewExprs
      }
      case Assign(l, FakeUse(e)) if e == l => Nop
      case Assign(l, e) if l == e => Nop
      case da @ DecAssign(l: LoSym, _, c: ConstExpr) => {
        knownValues(l) = c
        da
      }
      case IfElse(True, o1, o2) => o1
      case IfElse(False, o1, o2) => o2
      case While(False, _) => Nop
      case _ => withNewExprs
    }
  }
}

object PropagateConstants {
  def apply(typed: TypedLoAst, replaceInsidePhi: Boolean=false): TypedLoAst = {
    val pc = new PropagateConstants(typed, replaceInsidePhi)
    val newAst = pc.rename(typed)
    TypedLoAst(newAst)
  }
}

