// See LICENSE.txt
package ressort.example
import scala.collection.mutable.{HashMap, LinkedHashMap, ArrayBuffer}
import ressort.hi._
import ressort.hi.compiler.{Hash64Generator}
import ressort.lo
import ressort.lo.Record
/** Ressort Library implementation of TPC-H Query 17
  *
  * Original specification (with validation parameters):
  * {{{
  * select
  *   sum(l_extendedprice) / 7.0 as avg_yearly
  * from
  *   lineitem,
  *   part
	* where
  * 	p_partkey = l_partkey
  * 	and p_brand = 'Brand#23'
  * 	and p_container = 'MED BOX' and l_quantity < (
  * 		select
  * 			0.2 * avg(l_quantity)
  * 		from
  * 			lineitem
  * 		where
  * 			l_partkey = p_partkey
  * 	);
	* }}}
	*/
class TpchQ17(tpch: TpchSchema.Generator, extraBits: Int=0, weave: Int=0) extends HiResTest {
  import ressort.hi.meta._
  import ressort.hi.meta.MetaParam._
  val nbits = (math.log(tpch.litemSize) / math.log(2.0)).toInt + extraBits
  val weaveStr = if (weave > 0) "_weave$weave" else ""
  val name = s"q17_man_${nbits}hb${weaveStr}"

  val input = tpch.allocate

  val litem = Concrete('lineitem_, TpchSchema.lineitem.s.fields.map(_.name.get.name).map(Id))
  val part = Concrete('part_, TpchSchema.part.s.fields.map(_.name.get.name).map(Id))

  val funcType = {
    Func(
      Map(
        'lineitem -> TpchSchema.lineitem,
        'part -> TpchSchema.part),
      lo.LoFloat())
	}

  val meta: MetaOp = {
    var ptable: MetaOp = part
    var join: MetaOp = litem

    val hash = HashConfig(width = 0, bits = Log2Up(Length('part)))

    ptable = ptable
      .filter('p_brand === TpchSchema.BRAND23, 'p_container === TpchSchema.MED_BOX)
      .asIncomplete
      .rename('p_partkey -> 'p_partkey)
      .aggregate().copy(groupBy='p_partkey::Nil)
      .asIncomplete

    join = join
      .equiJoin(ptable, 'l_partkey, 'p_partkey)
        .withBuild(false)
        .withGather(false)
      .asIncomplete
      .rename(
        'l_partkey -> 'l_partkey,
        'l_quantity -> Cast('l_quantity, lo.LoDouble()),
        'l_extendedprice -> Cast('l_extendedprice, lo.LoDouble()))

    var ltable: MetaOp = join
    ltable = ltable
      .rename(
        'l_partkey_table -> 'l_partkey,
        'l_quantity -> 'l_quantity,
        'count -> DoubleConst(1.0))
      .aggregate(
        'l_quantity -> PlusOp,
        'count -> PlusOp).copy(groupBy = 'l_partkey_table :: Nil)
      .asIncomplete
      .rename(
        'l_partkey_table -> 'l_partkey_table,
        'avg -> DoubleConst(0.2) * 'l_quantity / 'count)

    join = join
      .equiJoin(ltable, 'l_partkey, 'l_partkey_table)
        .withBuild(false)
        .withGather(false)
      .filter('l_quantity < 'avg)
      .asIncomplete

    join = join
      .aggregate('l_extendedprice -> PlusOp)
      .rename('avg_yearly -> UField(0) / DoubleConst(7.0))

    join.nestedSumDouble('avg_yearly).cast(UField(0), lo.LoFloat())
  }

  val hiRes: Operator = {
    Let(
      List(
        'part_ := 'part,
        'lineitem_ := 'lineitem),
    in = meta.allOps.head)
  }

  /** In the default query plan for TPC-H Q17, we pre-compute the correlated aggregation
    * sub-query for each `l_partkey` in `lineitem`.
    */
  val oldHiRes: Operator = {
    Let(
      List(
        'lineitem := 'lineitem,
        'part := 'part,
        'htbl := 
          HashTable(
            'lineitem.project(
              'l_partkey -> 'l_partkey,
              'l_quantity -> 'l_quantity,
              'count -> DoubleConst(1.0)),
            aggregates = List((NFieldName('l_quantity), PlusOp), (NFieldName('count), PlusOp)),
            hash = Some(Hash64('lineitem('l_partkey), nbits)),
            buckets = Some(1 << nbits)
          ),
        'litem_htbl := Cat(Shell('lineitem), 'htbl, Shell('part)),
        'lineitem := Flatten(Uncat('litem_htbl, 0)),
        'htbl := Uncat('litem_htbl, 1),
        'part := Flatten(Uncat('litem_htbl, 2)),
        'hist := Offsets('htbl),
        'cat := Cat('htbl, Shell('hist)),
        'htbl := Block(Block(Uncat('cat, 0), nonFusable=true), true),
        'hist := Flatten(Uncat('cat, 1)),
        'p2_avg_qty := 'htbl(DoubleConst(0.2) * 'l_quantity / 'count),
        'l_partkey := 'htbl('l_partkey),
        'avg_tbl := Compact(Project('l_partkey, 'p2_avg_qty), hist=Some('hist)),
        'avg_tbl := Block('avg_tbl, true),
        'cat := Cat(Shell('part), 'avg_tbl),
        'part := Flatten(Uncat('cat, 0)),
        'avg_tbl := Uncat('cat, 1),
        'part_tbl :=
          HashTable(
            Let(
              List(
                'pcond := 'part(
                  ('p_brand === TpchSchema.BRAND23) &&
                  ('p_container === TpchSchema.MED_BOX)),
                'part := Mask('part, 'pcond)
              ),
              'part('p_partkey)
            ),
            hash = Some(Hash64('part('p_partkey), nbits)),
            buckets = Some(1 << nbits)
          ),
        'cat := Cat(Shell('part), Shell('lineitem), 'part_tbl),
        'part := Flatten(Uncat('cat, 0)),
        'lineitem := Flatten(Uncat('cat, 1)),
        'part_tbl := Uncat('cat, 2),
        'ljoin :=
          HashJoin(
            left = Shell('lineitem).project(
              'l_partkey_left -> 'l_partkey,
              'l_quantity -> 'l_quantity,
              'l_extendedprice -> 'l_extendedprice),
            right = 'avg_tbl,
            hash = Hash64(Shell('lineitem)('l_partkey), nbits),
            test = Some(('l_partkey_left === 'l_partkey) && ('l_quantity.toLoDouble < 'p2_avg_qty))),
        'lflat := Flatten(Compact(
          ('ljoin), hist=Some(Offsets('ljoin)))),
        'pjoin :=
          HashJoin(
            left = Shell('lflat),
            right = 'part_tbl,
            hash = Hash64(Shell('lflat)('l_partkey), nbits)),
        'pflat := 
            Compact(
              Block('pjoin, nest=true).project('avg_yearly -> 'l_extendedprice.toLoDouble / 7.0),
              hist=Some(Offsets('pjoin))
            ),
        'avg_yearly := 
          NestedSumDouble(
            SumDouble(
              'pflat('avg_yearly)))
        ),
        in = 'avg_yearly(UField(0).toLoFloat))
  }

  override val check = {
    case class LRec(sum_qty: Double, count: Long)
    val ltbl = HashMap[Long, LRec]()
    for (i <- tpch.l_extendedprice.indices) {
      val pkey = tpch.l_partkey(i)
      val qty = tpch.l_quantity(i)
      val rec = ltbl.getOrElse(pkey, LRec(0.0, 0))
      ltbl(pkey) = rec.copy(sum_qty = rec.sum_qty + qty, count = rec.count + 1)
    }

    val ptbl = LinkedHashMap[Long, ArrayBuffer[Long]]()
    for (i <- tpch.p_partkey.indices) {
      val pkey = tpch.p_partkey(i)
      val brand = tpch.p_brand(i)
      val cont = tpch.p_container(i)
      val hash = Hash64Generator.multHashStatic(pkey, nbits)
      if ((brand == TpchSchema.BRAND23.n) && (cont == TpchSchema.MED_BOX.n)) {
        if (!ptbl.contains(hash)) {
          ptbl(hash) = ArrayBuffer()
        }
        ptbl(hash).append(pkey)
      }
    }

    var sum = 0.0
    val pjoin = ArrayBuffer[Float]()
    for (i <- tpch.l_extendedprice.indices) {
      val pkey = tpch.l_partkey(i)
      val qty = tpch.l_quantity(i)
      val price = tpch.l_extendedprice(i)
      val hash = Hash64Generator.multHashStatic(pkey, nbits)
      val prec = ptbl.getOrElse(hash, ArrayBuffer())
      val lrec = ltbl(pkey)
      if ((qty < 0.2 * lrec.sum_qty / lrec.count) && prec.contains(pkey)) {
        pjoin += price / 7.0.toFloat
        sum += price
      }
    }
    sum = sum / 7.0

    //val arr = lo.Deref(lo.Deref('result).dot('arr))

    /**
    case class LJRec(l_partkey: Long, l_quantity: Long, l_extendedprice: Float, p2_avg_qty: Float)
    val ljoin = ArrayBuffer[LJRec]()
    for (i <- tpch.l_extendedprice.indices) {
      val pkey = tpch.l_partkey(i)
      val qty = tpch.l_quantity(i)
      val price = tpch.l_extendedprice(i)
      val lrec = ltbl(pkey)
      val p2a = 0.2 * lrec.sum_qty / lrec.count
      if (qty < p2a)
        ljoin += LJRec(l_partkey = pkey, l_quantity = qty, l_extendedprice = price, p2_avg_qty = p2a.toFloat)
    }
    Some(HiResTest.checkArrLong(ljoin.map(_.l_partkey).toArray, arr, Some(x => lo.Field(x, 'l_partkey))))
    Some(HiResTest.checkArrFloat(ljoin.map(_.p2_avg_qty).toArray, arr, Some(x => lo.Field(x, 'p2_avg_qty))))

    Some(HiResTest.checkArrFloat(pjoin.toArray, arr, Some(x => lo.Field(x, 'avg_yearly))))
    **/

    //Some(HiResTest.checkArrLong(ptbl.values.flatten.toArray, arr))

    val res = lo.Deref(lo.Deref('result).dot('arr)).sub(0)
    Some(HiResTest.checkScalarFloat(sum.toFloat, res))

  }

}
