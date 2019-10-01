// See LICENSE.txt
package ressort.lo.compiler
import ressort.compiler.cpp._
import ressort.lo

/** Implements the translation of LoRes array operations into C++
  *
  * The default implementation generates serial C++ code; other
  * translator targets will convert these to the appropriate 
  * platform-specific parallel primitives.
  */
class CppArrOpTranslator {
  def translate(
      ir: lo.TypedLoAst,
      aop: lo.ArrOp): CppAst = {
    implicit val ast = ir
    aop match {
      case ps: lo.PrefixSum => prefixSumTrans(ps)
      case ms: lo.Memset => memsetTrans(ms)
      case rr: lo.RotRight => rotRightTrans(rr)
      case _ => ???
    }
  }

  /** Returns the C++ lvalue corresponding to the LoRes array on which this
    * [[lo.ArrOp]] operates.
    */
  def getCppArr(aop: lo.ArrOp)
      (implicit ast: lo.TypedLoAst): Expr = {
        
    Expr(ast.scope(aop.opArr))
  }

  /** Returns a C++ [[Expr]] for the start and end indices of this op */
  def getRange(aop: lo.ArrOp)
      (implicit ast: lo.TypedLoAst): (Expr, Expr) = {
        
    aop.opRange match {
      case Some(r) => Pair(Expr(ast.scope(r.start)), Expr(ast.scope(r.end)))
      case None => {
        val errStr = "ExplicitRanges transform failed: "+aop
        throw new AssertionError(errStr)
      }
    }
  }

  /** Returns a C++ expression for the number of elements processed by `aop` */
  def getLen(aop: lo.ArrOp)
      (implicit ast: lo.TypedLoAst): Expr = {
        
    val (start, end) = getRange(aop)
    Minus(end, start)
  }

  def prefixSumTrans(aop: lo.PrefixSum)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    val cppArr = getCppArr(aop)
    val intType = CppType(ast.scope(aop.arr.sub(0)).loType)
    val (start, end) = getRange(aop)
    val tmp = TmpId("tmp")
    val acc = TmpId("acc")
    val i = TmpId("i")

    Block(List(
      Dec(tmp, intType, Some(Const(0))),
      Dec(acc, intType, Some(Const(0))),
      For(
        Dec(i, SizeT(), Some(start)),
        Lt(i, end),
        Assign(i, Plus(i, Const(1))),
        Block(List(
          Assign(tmp, Subsc(cppArr, i)),
          Assign(Subsc(cppArr, i), acc),
          Assign(acc, Plus(acc, tmp))
        )))
    ))
  }

  def memsetTrans(aop: lo.Memset)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    val cppValue = Expr(ast.scope(aop.value))
    val valueType = CppType(ast.scope(aop.value).loType)
    val (start, end) = getRange(aop)
    val i = TmpId("i")
    val cppArr = getCppArr(aop)

    val forLoop = { 
      For(
        Dec(i, SizeT(), Some(start)),
        Lt(i, end),
        Assign(i, Plus(i, Const(1))),
          Assign(Subsc(cppArr, i), cppValue))
    }

    val memset = {
      val nbytes = Mul(getLen(aop), Sizeof(valueType))
      val arrPtr = Plus(cppArr, start)
      CallStmt(Call(Id("memset"), List(arrPtr, Const(0), nbytes)))
    }

    cppValue match {
      case Const(0) => memset
      case _ => forLoop
    }
  }

  def rotRightTrans(aop: lo.RotRight)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    val (start, end) = getRange(aop)
    val elemType = CppType(ast.scope(aop.opArr.sub(lo.Const(0))).loType)
    val shift = Expr(ast.scope(aop.shamt))
    val len = getLen(aop)
    val cppArr = getCppArr(aop)

    val startC = TmpId("start")
    val endC = TmpId("end")
    val lenC = TmpId("len")
    val indexC = TmpId("index")
    val i = TmpId("i")
    val acc = TmpId("acc")
    val tmp = TmpId("tmp")

    Block(List(
      Dec(startC, SizeT(true), Some(start)),
      Dec(endC, SizeT(true), Some(end)),
      Dec(lenC, SizeT(true), Some(len)),
      Dec(acc, elemType, None),
      Dec(tmp, elemType, Some(Subsc(cppArr, startC))),
      For(
        Dec(i, SizeT(), Some(startC)),
        Lt(i, endC),
        Assign(i, Plus(i, Const(1))),
        Block(List(
          Assign(acc, tmp),
          Dec(indexC, SizeT(true), Some(Plus(startC, Mod(Plus(i, shift), lenC)))),
          Assign(tmp, Subsc(cppArr, indexC)),
          Assign(Subsc(cppArr, indexC), acc)
        ))
      )
    ))
  }
}
