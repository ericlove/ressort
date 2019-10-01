// See LICENSE.txt
package ressort.example
import ressort.hi.{Func, Operator}
import ressort.lo
import ressort.lo.interp
/** A test of the whole Ressort compiler that combines `HiRes` code with a validator in `LoRes`
  *
  * If the `check` option is set, it should follow ths convention:
  *   - It should fill `input` with `LoRes` code to allocate and fill any inputs to the compiled operator
  *   - It should assume `result` is assigned the result of calling the compiled `LoRes` function
  *   - It should set the `flag` variable to true if the result is correct
  *
  * For example, the `check` epilogue to an implementation of TPC-H Query 6 might incude:
  * {{{
  *
  *   ...
  *
  *   lineitem0->l_linestatus->len := 300000
  *   lineitem0->l_linestatus->items := Alloc[ArrExpr(UInt8(false),lineitem0->l_linestatus->len)]
  *   For(i3 = 0...300000 by 1) {
  *       Deref(lineitem0->l_shipmode->items)[i3] := Escape(i3,Index(false),UInt8(false),<function1>)
  *       Deref(lineitem0->l_shipinstruct->items)[i3] := Escape(i3,Index(false),UInt8(false),<function1>)
  *       Deref(lineitem0->l_quantity->items)[i3] := Escape(i3,Index(false),UInt32(false),<function1>)
  *       Deref(lineitem0->l_shipdate->items)[i3] := Escape(i3,Index(false),UInt16(false),<function1>)
  *       Deref(lineitem0->l_extendedprice->items)[i3] := Escape(i3,Index(false),LoFloat(false),<function1>)
  *       Deref(lineitem0->l_partkey->items)[i3] := Escape(i3,Index(false),UInt32(false),<function1>)
  *       Deref(lineitem0->l_discount->items)[i3] := Escape(i3,Index(false),LoFloat(false),<function1>)
  *   }
  *   var result: ptr_struct__lo_arr_float
  *   result := q06(lineitem=lineitem0)
  *   Nop
  *   t70 := Deref(result->arr->items)[0]
  *   t72 := t70-(2246665.8)
  *   t75 := (t72*t72)<(1.0E-7)
  *   var flag: bool
  *   If (t75) {
  *       Printf("%f : CORRECT\n", 2246665.8)
  *   } else {
  *       Printf("%f where %f expected : WRONG\n", t70, 2246665.8)
  *   }
  *   flag := Mux(t75,True,False)
  * }}}
  *
  * @param hiRes The `HiRes` input to be compiled and tested.
  * @param funcType The function type of `hiRes`
  * @param name The name of the compiled function to be called
  * @param check `LoRes` code to be appended to the compiled `hiRes` to check its result
  * */
trait HiResTest  { //extends FunSpec with GivenWhenThen {
  def hiRes: Operator

  def funcType: Func

  def name: String

  def input: lo.LoAst

  def check: Option[lo.LoAst] = None
}

object HiResTest {

  def checkScalarFloat(correct: Float, result: lo.Expr): lo.LoAst = {
    import lo._
    DecAssign('err, lo.LoFloat(), result - FloatConst(correct)) +
    IfElse ( Mul('err,  'err) < FloatConst(1e-7.toFloat),
      Printf("%f : CORRECT\n", FloatConst(correct.toFloat)),
      Printf("%f where %f expected : WRONG\n", result, FloatConst(correct.toFloat)) + ('flag := False))

  }

  def checkArrFloat(correct: Array[Float], result: lo.LValue, field: Option[lo.LValue=>lo.LValue]=None): lo.LoAst = {
    import lo._
    val value = field.map(f => f(result.sub('i))).getOrElse(result.sub('i))
    Printf("Checking array [%d]", correct.length) +
    ForBlock('i, correct.length,
      DecAssign(
        'corr,
        lo.LoFloat(),
        Escape('i, lo.LoInt(), lo.LoFloat(),
        n => lo.interp.EFloat(correct(n.toEInt(None).i.toInt)))) +
      DecAssign('err, lo.LoFloat(), value - 'corr) +
      IfElse ( Mul('err,  'err) < FloatConst(1e-7.toFloat),
        Nop,//Printf("%d: %f : CORRECT\n", 'i, 'corr),
        Printf("%d: %f where %f expected : WRONG\n", 'i, Cast(value, LoFloat()), 'corr) +
        ('flag := False)
      ))
  }

  def checkArrLong(correct: Array[Long], result: lo.LValue, field: Option[lo.LValue=>lo.LValue]=None): lo.LoAst = {
    import lo._
    val value = field.map(f => f(result.sub('i))).getOrElse(result.sub('i))
    Printf("Checking array [%d]", correct.length) +
    ForBlock('i, correct.length,
      DecAssign(
        'corr,
        lo.Index(),
        Escape('i, lo.LoInt(), lo.Index(),
        n => lo.interp.EInt(correct(n.toEInt(None).i.toInt), lo.Index()))) +
      IfElse ( Equal(value, 'corr),
        Nop,//Printf("%d: %d : CORRECT\n", 'i, 'corr),
        Printf("%d: %d where %d expected : WRONG\n", 'i, Cast(value, Index()), 'corr) +
        ('flag := False)
      ))
  }
}
