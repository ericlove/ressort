// See LICENSE.txt
package ressort.example
import ressort.lo
import ressort.hi._
import scala.collection.mutable.HashMap

/** Ressort Library implementations of TPC-H Query 1
  *
  * Original specification:
  * {{{
  * select
  *   l_returnflag,
  *   l_linestatus,
  *   sum(l_quantity) as sum_qty,
  *   sum(l_extendedprice) as sum_base_price,
  *   sum(l_extendedprice*(1-l_discount)) as sum_disc_price,
  *   sum(l_extendedprice*(1-l_discount)*(1+l_tax)) as sum_charge,
  *   avg(l_quantity) as avg_qty,
  *   avg(l_extendedprice) as avg_price,
  *   avg(l_discount) as avg_disc,
  *   count(*) as count_order
  * from
  *   lineitem
  * where
  *   l_shipdate <= date '1998-12-01' - interval '[DELTA]' day (3)
  * group by
  *   l_returnflag, l_linestatus
  * order by
  *   l_returnflag, l_linestatus;
  * }}}
  */
class TpchQ01(tpch: TpchSchema.Generator) extends HiResTest {
  val name = "q01"

  val input = tpch.allocate

  val outRec =
    lo.FlatRecord(
      fields =
          Seq(
            'l_returnflag -> lo.UInt8(),
            'l_linestatus -> lo.UInt8(),
            'sum_qty -> lo.UInt32(),
            'sum_base_price -> lo.LoFloat(),
            'sum_disc_price -> lo.LoFloat(),
            'sum_charge -> lo.LoFloat(),
            'avg_qty -> lo.LoFloat(),
            'avg_price -> lo.LoFloat(),
            'avg_disc -> lo.LoFloat(),
            'count_order -> lo.UInt32()
          ),
      name = Some('h),
      const = false
    )

  val funcType = {
    Func(
      Map(
        'lineitem -> TpchSchema.lineitem),
      Vec(outRec))
  }


  val maxShipdate = (1998 - 1992) * 365 + 12 * 31 - 90

  val allFields = outRec.fields.map(f => Id(f.name.get.name))

  val meta = {
    import ressort.hi.meta._
    import ressort.hi.meta.MetaParam._
    val litem = Concrete('lineitem, TpchSchema.lineitem.s.fields.map(_.name.get.name).map(Id).toSet)
    var m: MetaOp = litem

    m = m
      .filter('l_shipdate < maxShipdate)
      .rename(
        'disc_price -> 'l_extendedprice * (FloatConst(1.0.toFloat) - 'l_discount))
        .copy(keepInput = true)
      .rename(
        'charge -> (('l_tax + 1.0.toFloat) * 'disc_price))
        .copy(keepInput = true)
      .rename(
        'count -> Const(1).toLoInt,
        'sum_qty -> 'l_quantity,
        'sum_base_price -> 'l_extendedprice,
        'sum_disc_price -> 'disc_price,
        'sum_charge -> 'charge,
        'sum_disc -> 'l_discount,
        'count_order -> Cast(Const(1), lo.UInt32()))
      .groupBy('l_returnflag, 'l_linestatus)
        .withAggregates(
          'sum_qty -> PlusOp,
          'sum_base_price -> PlusOp,
          'sum_disc_price -> PlusOp,
          'sum_charge -> PlusOp,
          'sum_disc -> PlusOp,
          'count_order -> PlusOp)
      .rename(
        'avg_qty -> 'sum_qty.toLoFloat / 'count_order.toLoFloat,
        'avg_price -> 'sum_price.toLoFloat / 'count_order.toLoFloat,
        'avg_disc -> 'sum_disc.toLoFloat / 'count_order.toLoFloat)
      .copy(keepInput = true)
      .rename()
    m
  }



  val hiRes = {
    meta.allOps.head
  }

  override val check: Option[lo.LoAst] = {


    val loRes = {
      import ressort.lo._
      import ressort.lo.interp.EFloat

      val sum_qty = HashMap[(Int, Int), Int]()
      val sum_base_price = HashMap[(Int, Int), Float]()
      val sum_disc_price = HashMap[(Int, Int), Float]()
      val sum_charge = HashMap[(Int, Int), Float]()
      val avg_qty = HashMap[(Int, Int), Float]()
      val avg_price = HashMap[(Int, Int), Float]()
      val avg_disc = HashMap[(Int, Int), Float]()
      var count = HashMap[(Int, Int), Int]()

      for (i <- 0 until tpch.litemSize) {
        if (tpch.l_shipdate(i) <= maxShipdate) {
          val pair = (tpch.l_returnflag(i), tpch.l_linestatus(i))
          import scala.Numeric.Implicits._
          def add[T : Numeric](hmap: HashMap[(Int, Int), T], n: T): Unit = {
            val init = hmap.getOrElse(pair, implicitly[Numeric[T]].zero)
            hmap(pair) = implicitly[Numeric[T]].plus(init, n)
          }
          add(sum_qty, tpch.l_quantity(i))
          add(sum_base_price, tpch.l_extendedprice(i))
          add(sum_disc_price, tpch.l_extendedprice(i) * (1.0.toFloat - tpch.l_discount(i)))
          add(sum_charge, tpch.l_extendedprice(i) * (1.0.toFloat - tpch.l_discount(i)) * (1.0.toFloat + tpch.l_tax(i)))
          add(avg_qty, tpch.l_quantity(i).toFloat)
          add(avg_price, tpch.l_extendedprice(i))
          add(avg_disc, tpch.l_discount(i))
          add(count, 1)
        }
      }

      def avg(hmap: HashMap[(Int, Int), Float]): Unit = {
        for ((pair, v) <- hmap) {
          hmap(pair) = v / count(pair).toFloat
        }
      }
      avg(avg_qty)
      avg(avg_price)
      avg(avg_disc)

      val pairs = sum_qty.keys.toList.sortWith((p1, p2) => if (p1._1 == p2._1) (p1._2 < p2._2) else false)
      val correct = HashMap[Symbol, Array[Float]]()
      for (s <- outRec.fields.map(_.name.get)) {
        correct(Symbol(s.name)) = Array.fill[Float](pairs.length)(0.0.toFloat)
      }
      val names = outRec.fields.map(_.name.get.toString)
      val col = names.map(_.length).max
      val format = outRec.fields.map(_ => s"%-${col}s").mkString("    ")
      println(format.format(names:_*))
      for (((rflag, lstat), i) <- pairs.zipWithIndex) {
        val p = (rflag, lstat)
        correct('l_returnflag)(i) = rflag
        correct('l_linestatus)(i) = lstat
        correct('sum_qty)(i) = sum_qty(p)
        correct('sum_base_price)(i) = sum_base_price(p)
        correct('sum_disc_price)(i) = sum_disc_price(p)
        correct('sum_charge)(i) = sum_charge(p)
        correct('avg_qty)(i) = avg_qty(p)
        correct('avg_price)(i) = avg_price(p)
        correct('avg_disc)(i) = avg_disc(p)
        correct('count_order)(i) = count(p)
        val fields = List(rflag, lstat, sum_qty(p), sum_base_price(p), sum_disc_price(p), sum_charge(p), avg_qty(p), avg_price(p), avg_disc(p), count(p))
        println(format.format(fields.map(_.toString.take(col)):_*))
      }

      val err = Id("err")
      val flag = Id("flag")
      val corr = Id("correct")
      val rec = Deref('result.dash('arr)).sub('i)
      val fieldTypes = outRec.fields.map(f => f.name.get -> f.loType).toMap
      tpch.allocateRelation(outRec, correct.toMap) +
      DecAssign(flag, Bool(), True) +
      Dec(err, LoFloat()) +
      ForBlock('i,  pairs.length,
        Block(
          (for (field <- correct.keys) yield {
            (corr := (LoFloat(), Cast(Escape('i, Index(), fieldTypes(field).loType, v => EFloat(correct(field)(v.toEInt(None).i.toInt))), LoFloat()))) +
                (err := rec.dot(field) - corr) +
                If((err * err) > FloatConst(0.001.toFloat),
                  Printf(s"$field was %f; should be %f", Cast(rec.dot(field), LoFloat()), corr) +
                      (flag := False)
                )
        }).toList))
    }
    Some(loRes)
  }


}
