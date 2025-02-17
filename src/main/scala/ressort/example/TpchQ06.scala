// See LICENSE.txt
package ressort.example
import ressort.hi._
import ressort.lo

class TpchQ06(threads: Int, crack: Boolean, collect: Boolean=false, tpch: Option[TpchSchema.Generator]=None, pad: Int=0, minDate: Int=TpchQ06.constants.minDate) extends HiResTest {
  val crackStr = if (crack) "_crack" else ""
  val collStr = if (collect) "_coll" else ""
  val mdStr = s"_${minDate}minDate"
  val name = s"q06_t${threads}${crackStr}${collStr}_${pad}pad$mdStr"

  val input = tpch.map(_.allocate).getOrElse(lo.Nop)

  val funcType = TpchQ06.funcType 

  val hiRes = TpchQ06.query(threads, crack, collect, minDate = minDate)

  override val check: Option[lo.LoAst] = this.tpch map { tpch =>
    var sum = 0.0.toDouble
    val myMinDate = minDate
    import TpchQ06.constants._
    for (i <- tpch.l_extendedprice.indices) {
      val date = tpch.l_shipdate(i)
      val disc = tpch.l_discount(i)
      val quant = tpch.l_quantity(i)
      if ((date > myMinDate) && (date < maxDate) &&
          (disc > minDiscount) && (disc < maxDiscount) &&
          (quant < maxQuantity)) {
          sum +=
              tpch.l_extendedprice(i).toDouble * disc.toDouble
      }
    }

    val loRes = {
      import ressort.lo._

      HiResTest.checkScalarFloat(sum.toFloat, Deref('result.dash('arr)).sub(0))
    }
    loRes
  }
}


object TpchQ06 {
  object constants {
    val minDate = 366*2
    val maxDate = 366*3
    val minDiscount = 0.05.toFloat
    val maxDiscount = 0.07.toFloat
    val maxQuantity = 24
  }

  import ressort.hi.meta._
  import ressort.hi.meta.MetaParam._

  val funcType = {
    Func(
      Map(
        'lineitem -> TpchSchema.lineitem),
      lo.LoFloat())
  }

  def query(threads: Int=1, crack: Boolean=false, collect: Boolean=false, pad: Int=0, minDate: Int=constants.minDate): Operator = {
    val litem = Concrete('lineitem, TpchSchema.lineitem.s.fields.map(_.name.get.name).map(Id))

    var meta: MetaOp = litem

    meta = meta
      .splitPar(Const(threads))
      .filter(
        'l_shipdate > minDate && 'l_shipdate < constants.maxDate,
        'l_discount > constants.minDiscount && 'l_discount < constants.maxDiscount,
        'l_quantity < constants.maxQuantity)
          .withCracked(crack).withCollect(collect)
          .asIncomplete
      .rename('revenue ->  Cast('l_extendedprice, lo.LoDouble()) * Cast('l_discount, lo.LoDouble()))
      .aggregate(('revenue, PlusOp))
      .nestedSumDouble('revenue, mute = threads < 2)
      .cast(UField(0), lo.LoFloat())

    meta.allOps.head

  }

}
