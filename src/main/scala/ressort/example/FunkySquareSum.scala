package ressort.example
import ressort.hi._
import ressort.lo

/** A fusion test case with multiple loops
  *
  * {{{
  *  select
  *   sum(((l_extendedprice * (1-l_discount)) - ravg)^2) as out
  *  from
  *     (select
  *        avg(l_extendedprice * (1-l_discount))
  *      from lineitem as ravg),
  *     lineitem
  *   where
  *     l_quantity > 100
  * }}}
  */
class FunkySquareSum(repeat: Boolean=false) extends HiResTest {
  val name = "funkySquare"

  val threads = 1

  val funcType = {
    Func(
      Map(
        'lineitem -> TpchSchema.lineitem),
      (lo.LoFloat()))
  }

  val input: lo.LoAst = lo.Nop

  val version1 = {
    Let(List(
      ('L := 'lineitem),
      ('t1 := 'L('l_extendedprice * (FloatConst(1.toFloat) - 'l_discount))),
      ('ravg :=
        Zip(SumFloat('t1), Count('t1))(UField(0) / UField(1))),
      ('t3 := 'L('l_quantity > 100)),
      ('t4 := Mask('t1, 't3)),
      ('t5 := Zip('t4, 'ravg)('t4 - 'ravg)),
      ('t6 := 't5(UField(0) * UField(0)))),
      in = SumFloat('t6))
  }

  val version2 = {
    Let(List(
      ('L := 'lineitem),
      ('t1 := 'L('l_extendedprice * (FloatConst(1.toFloat) - 'l_discount))),
      ('ravg :=
        Zip(SumFloat('t1), Count('t1))(UField(0) / UField(1))),
      ('t3 := 'L('l_quantity > 100)),
      ('t4 := Mask('L, 't3)('l_extendedprice * (FloatConst(1.toFloat) - 'l_discount))),
      ('t5 := Zip('t4, 'ravg)('t4 - 'ravg)),
      ('t6 := 't5(UField(0) * UField(0)))),
      in = SumFloat('t6))
  }

  val hiRes = {
    Let(List(
      ('L := 'lineitem),
      ('t1 := 'L('l_extendedprice * (FloatConst(1.toFloat) - 'l_discount))),
      ('ravg :=
          Zip(SumFloat('t1), Count('t1))(UField(0) / UField(1))),
      ('t3 := 'L('l_quantity > 100)),
      ('t4 := {
        if (repeat)
          Mask('L, 't3)('l_extendedprice * (FloatConst(1.toFloat) - 'l_discount))
        else
          Mask('t1, 't3)
      }),
      ('t5 := Zip('t4, 'ravg)('t4 - 'ravg)),
      ('t6 := 't5(UField(0) * UField(0)))),
      in = SumFloat('t6))
  }
}

