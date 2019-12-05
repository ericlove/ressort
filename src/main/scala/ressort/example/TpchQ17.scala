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

    val bits = Log2Up(Length('part))
    val hash = HashConfig(width = 0, bits = bits, msb = bits - 1)

    ptable = ptable
      .filter('p_brand === TpchSchema.BRAND23, 'p_container === TpchSchema.MED_BOX)
      .asIncomplete
      .rename('valid -> 'valid, 'p_partkey -> 'p_partkey)
      .aggregate()
        .copy(groupBy='p_partkey::Nil, hash = hash)
        .copy(overflow=false, implicitMask=true)
      .asIncomplete

    join = join
      .equiJoin(ptable, 'l_partkey, 'p_partkey)
        .copy(overflow=false, implicitMask=true)
        .withBuild(false)
        .withGather(false)
        .withHash(hash)
      .rename(
        'l_partkey -> 'l_partkey,
        'l_quantity -> Cast('l_quantity, lo.LoDouble()),
        'l_extendedprice -> Cast('l_extendedprice, lo.LoDouble()))
      .flatten

    var ltable: MetaOp = join
    ltable = ltable
      .rename(
        'valid -> True,
        'l_partkey_table -> 'l_partkey,
        'l_quantity -> 'l_quantity,
        'count -> DoubleConst(1.0))
      .aggregate('l_quantity -> PlusOp, 'count -> PlusOp)
        .copy(groupBy = 'l_partkey_table :: Nil, overflow=false, implicitMask=true, hash=hash)
      .asIncomplete
      .rename(
        'valid -> 'valid,
        'l_partkey_table -> 'l_partkey_table,
        'avg -> DoubleConst(0.2) * 'l_quantity / 'count)

    join = join
      .equiJoin(ltable, 'l_partkey, 'l_partkey_table)
        .withBuild(false)
        .withGather(false)
        .withHash(hash)
        .copy(overflow=false, implicitMask=true)
        .asIncomplete
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

    val res = lo.Deref(lo.Deref('result).dot('arr)).sub(0)
    Some(HiResTest.checkScalarFloat(sum.toFloat, res))

  }

}
