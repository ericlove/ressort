// See LICENSE.txt
package ressort.example
import ressort.util.log2Up
import ressort.Ressort
import ressort.lo
import ressort.hi._

import TpchSchema.{
  BRAND12, BRAND23, BRAND34,
  SM_BOX, SM_CASE, SM_PACK, SM_PKG,
  MED_BAG, MED_BOX, MED_PKG, MED_PACK,
  LG_CASE, LG_PACK, LG_BOX, LG_PKG
}

abstract class TpchQ19(tpch: Option[TpchSchema.Generator]) extends HiResTest {
  val input = tpch.map(_.allocate).getOrElse(lo.Nop)

  val funcType = TpchQ19.funcType

  override val check: Option[lo.LoAst] = tpch map { tpch =>
    import ressort.lo._
    var sum = 0.0
    for (i <- tpch.l_shipinstruct.indices) {
      val instruct = tpch.l_shipinstruct(i)
      val mode = tpch.l_shipmode(i)
      if (instruct == TpchSchema.DELIVER_IN_PERSON.n && (mode == TpchSchema.AIR.n || mode == TpchSchema.AIR_REG.n)) {
        val l_quantity = tpch.l_quantity(i)
        val k = tpch.l_partkey(i)
        val p_brand = tpch.p_brand(k)
        val p_container = tpch.p_container(k)
        val p_size = tpch.p_size(k)

        val cond = (p_brand == BRAND12.n
              && (p_container == SM_CASE.n || p_container == SM_BOX.n || p_container == SM_PACK.n || p_container == SM_PKG.n)
              && l_quantity >= 1 && l_quantity <= 1 + 10 && 1 <= p_size && p_size <= 5) ||
              (p_brand == BRAND23.n &&
                  (p_container == MED_BAG.n || p_container == MED_BOX.n || p_container == MED_PKG.n || p_container == MED_PACK.n)
                  && l_quantity >= 10 && l_quantity <= 10 + 10 && 1 <= p_size && p_size <= 10) ||
              (p_brand == BRAND34.n &&
                  (p_container == LG_CASE.n || p_container == LG_BOX.n || p_container == LG_PACK.n || p_container == LG_PKG.n)
                  && l_quantity >= 20 && l_quantity <= 20 + 10 && 1 <= p_size && p_size <= 15)
        if (cond) {
          val l_extendedprice = tpch.l_extendedprice(i).toDouble
          val l_discount = tpch.l_discount((i)).toDouble
          sum += l_extendedprice * (1.0 - l_discount)
        }
      }
    }

    HiResTest.checkScalarFloat(sum.toFloat, Deref('result.dash('arr)).sub(0))
  }
}

trait Q19Auto { this: TpchQ19 =>
  import ressort.hi.meta._
  import ressort.hi.meta.MetaParam._

  val litem = Concrete('lineitem_, TpchSchema.lineitem.s.fields.map(_.name.get.name).map(Id))
  val part = Concrete('part_, TpchSchema.part.s.fields.map(_.name.get.name).map(Id))

  val postCond = 
  ('p_brand === BRAND12.n
    && ('p_container === SM_CASE.n || 'p_container === SM_BOX.n || 'p_container === SM_PACK.n || 'p_container === SM_PKG.n)
    && 'l_quantity >= Const(1) && 'l_quantity <= Const(1) + Const(10) && Const(1) <= 'p_size && 'p_size <= Const(5)) ||
  ('p_brand === BRAND23.n &&
    ('p_container === MED_BAG.n || 'p_container === MED_BOX.n || 'p_container === MED_PKG.n || 'p_container === MED_PACK.n)
    && 'l_quantity >= Const(10) && 'l_quantity <= Const(10) + Const(10) && Const(1) <= 'p_size && 'p_size <= Const(10)) ||
  ('p_brand === BRAND34.n &&
    ('p_container === LG_CASE.n || 'p_container === LG_BOX.n || 'p_container === LG_PACK.n || 'p_container === LG_PKG.n)
    && 'l_quantity >= Const(20) && 'l_quantity <= Const(20) + Const(10) && Const(1) <= 'p_size && 'p_size <= Const(15))


  def meta: MetaOp

  def hiRes: Operator = {
    Let(
      List(
        'part_ := 'part,
        'lineitem_ := 'lineitem),
    in = meta.allOps.head)
  }
}

case class TpchQ19Simple(tpch: Option[TpchSchema.Generator]) extends TpchQ19(tpch) with Q19Auto {
  import ressort.hi.meta._
  import ressort.hi.meta.MetaParam._
  override val name = s"Q19Simple"
  val totalBits = new ParamList[Expr](List(Log2Up(tpch.get.partSize)))
  val joinBits = new ExprParam(totalBits, e => e + Const(-6))
  val joinHash = HashConfig(bits = joinBits)
  import ressort.lo.{LoFloat, LoDouble}
  val partLen = tpch.map(_.partSize).getOrElse(60e5.toInt)
  val meta = {
    litem
        .withParams(totalBits)
        .shell
        .filter(
            ('l_shipinstruct === TpchSchema.DELIVER_IN_PERSON),
            ('l_shipmode === TpchSchema.AIR || 'l_shipmode === TpchSchema.AIR_REG))
        .equiJoin(part.rename(), 'l_partkey,'p_partkey)
            .withHash(HashConfig(bits = Log2Up(Length('part))))
        .filter(postCond)
        .rename('price ->
            Cast('l_extendedprice, LoDouble()) * (DoubleConst(1.0) - 'l_discount))
        .aggregate(('price, PlusOp))
        .nestedSumDouble(UField(0))
        .cast(UField(0), LoFloat())
  }

}

case class TpchQ19AutoNopa(
    tpch: Option[TpchSchema.Generator],
    threads: Int=4,
    useHash: Boolean=false,
    slots: Expr = Const(2),
    buildPartitioned: Boolean=false,
    blockBuild: Boolean=true,
    earlyMat: Boolean=true,
    inline: Boolean=false,
    compact: Boolean=false,
    array: Boolean=true
  ) extends TpchQ19(tpch) with Q19Auto {
  import ressort.hi.meta._
  import ressort.hi.meta.MetaParam._
  override val name = {
    val threadsStr = s"_${threads}t"
    val useHashStr = if (useHash) "_h64" else ""
    val slotsStr = s"_${slots}s"
    val compactStr = if (compact) "_cpct" else ""
    val earlyMatStr = if (earlyMat) "_em" else ""
    val blockBuildStr = if (blockBuild) "_blockBuild" else ""
    val buildPartitionedStr = if (buildPartitioned) "_bpart" else ""
    val inlineStr = if (inline) "_inline" else ""
    val arrayStr = if (array) "_array" else ""
    s"q19nopa$threadsStr$useHashStr$slotsStr$compactStr$buildPartitionedStr$earlyMatStr$inlineStr$blockBuildStr$arrayStr"
  }

  val totalBits = new ParamList[Expr](List(Log2Up(Length('part)/slots)))
  val joinBits = new ExprParam(totalBits, e => e)
  val msb = new ExprParam(totalBits, e => e - Const(1))
  val joinHash = HashConfig(
    bits = joinBits, 
    width = (if (array || !useHash) 0 else 64),
    msb = (if (array || !useHash) msb else Const(64))
  )

  val meta = {
    var table: MetaOp = part
    if (threads > 1 && buildPartitioned) table = table.splitPar(threads)
    if (earlyMat && !buildPartitioned) table = table.rename()
    var values = if (earlyMat) table.rename() else table

    if (array && !buildPartitioned)
      table = table.prepend('valid -> True)

    var join: MetaOp = litem
      .withParams(totalBits)

    join = join
      .splitPar(threads)
      .filter(
        ('l_shipinstruct === TpchSchema.DELIVER_IN_PERSON),
        ('l_shipmode === TpchSchema.AIR || 'l_shipmode === TpchSchema.AIR_REG))
      .asIncomplete
      .rename()

    join = join
      .equiJoin(table, 'l_partkey, 'p_partkey)
        .withOverflow(!array, array)
        .withHash(joinHash)
        .withCompactTable(compact)
        .withInlineCounter(inline)
        .withGather(!earlyMat)
        .withSlots(slots)
        .withBlockBuild(blockBuild)
        .withBlockHash(false)
        .withPartition(partition=buildPartitioned, parallelPart=threads>1)
        .asIncomplete
        .withRightRenamed(rightRenamed = (if (blockBuild && buildPartitioned) Some(values) else None))

    join
      .filter(postCond).asIncomplete
      .rename('price -> Cast('l_extendedprice, lo.LoDouble()) * (DoubleConst(1.0) - 'l_discount))
      .aggregate(('price, PlusOp))
      .rename('price -> Cast('price, lo.LoDouble()))
      .connector(o => NestedSumDouble(o('price))(Cast(UField(0), lo.LoFloat())))
  }

}

class TpchQ19AutoPart(
    val tpch: Option[TpchSchema.Generator],
    val partAll: Boolean=false,
    val partBits: Expr = Const(6),
    val subBits: Expr = Const(0),
    val useHash: Boolean=false,
    val threads: Int=16,
    val preThreads: Int=0,
    val postThreads: Int=0,
    val slots: Int=1,
    val compact: Boolean=false,
    val earlyMatTable: Boolean=true,
    val earlyMat: Boolean=true,
    val buildPartitioned: Boolean=false,
    val blockBuild: Boolean=true,
    val blockProbe: Boolean=true,
    val twoSided: Boolean=false,
    val threadLocal: Boolean=true,
    val inline: Boolean=true,
    val array: Boolean=true)
  extends TpchQ19(tpch) with Q19Auto {

  assert(threadLocal || (preThreads == 0 && postThreads == 0))

  val name = {
    val threadsStr = s"_${threads}t"
    val slotsStr = s"_${slots}s"
    val useHashStr = if (useHash) "_h64" else ""
    val compactStr = if (compact) "_cpct" else ""
    val earlyMatTableStr = if (earlyMatTable) "_pem" else ""
    val earlyMatStr = if (earlyMat) "_em" else ""
    val buildPartitionedStr = if (buildPartitioned) "_bpart" else ""
    val inlineStr = if (inline) "_inline" else ""
    val nbitsStr = partBits match {
      case Const(n) => s"_nbits$n"
      case _ =>
    }
    val twoSideStr = if (twoSided) "_twos" else ""
    val threadLocalStr = if (threadLocal) "_tlocal" else ""
    val preThreadsStr = s"_${preThreads}prth"
    val postThreadsStr = s"_${postThreads}psth"
    val subBitsStr = s"_${subBits}sb"
    val arrayStr = if (array) "_array" else ""
    val allStr = if (partAll) "all" else "single"
    s"q19part$allStr$threadsStr$useHashStr$nbitsStr$subBitsStr$slotsStr$compactStr" +
      s"$buildPartitionedStr$earlyMatTableStr$earlyMatStr$inlineStr$twoSideStr" +
      s"$threadLocalStr$preThreadsStr$postThreadsStr$arrayStr"
  }

  import ressort.hi.meta._
  import ressort.hi.meta.MetaParam._
  val totalBits = new ParamList[Expr](List(Log2Up(Length('part)) - (if (array) 0 else subBits)))
  val joinBits = new ExprParam(totalBits, e => (if (twoSided) (e - partBits) else e))
  val joinMsb = new ExprParam(totalBits, e => (if (twoSided) (e - partBits - Const(1)) else (e-1)))
  val partMsb = new ExprParam(totalBits, e => e - Const(1))
  val width = if (useHash && !array) 64 else 0
  val partHash = HashConfig(bits = partBits, msb = partMsb, width = width)
  val joinHash = HashConfig(bits = joinBits, msb = joinMsb, width = width)

  val meta = {
    var table: MetaOp = part

    val probeDepth = {
      var d = 0
      if (threads > 1) d += 1
      if (threadLocal && threads > 1) d += 1
      if (postThreads > 1) d += 1
      if (preThreads > 1) d += 1
      d
    }

    val buildDepth = if (twoSided) 1 else 0

    println(s"Probe depth $probeDepth; build depth $buildDepth")

    for (i <- buildDepth until probeDepth)
      table = table.shell

    if (twoSided) {
      table = table.splitPar(threads)
      table =
        table
          .partition('p_partkey, renamed = (if (partAll) Some(_.rename()) else None))
          .withHash(partHash)
          .withBlock(blockBuild)
          .withGather(!partAll)
          .withParallel(threads > 1)
    } else  {
      if (threads > 1 && buildPartitioned) table = table.splitPar(threads)
      if (!blockBuild) table = table.rename()
    }
    var values = if (earlyMatTable) table.rename() else table
    if (array && !buildPartitioned)
      table = table.prepend('valid -> True)


    var join: MetaOp = litem.withParams(totalBits)

    join = join
      .splitSeq(preThreads)
      .splitPar(threads)
      .splitSeq(postThreads)
      .filter(
        ('l_shipinstruct === TpchSchema.DELIVER_IN_PERSON),
        ('l_shipmode === TpchSchema.AIR || 'l_shipmode === TpchSchema.AIR_REG))
      .asIncomplete
      .partition('l_partkey, renamed = (if (partAll) Some(_.rename()) else None))
        .withHash(partHash)
        .withParallel(threads > 1 && !threadLocal)
        .withGather(!partAll)
        .withBlock(blockProbe)

    join = join.shell

    join = join
      .equiJoin(table, 'l_partkey,'p_partkey)
        .withOverflow(!array, array)
        .withHash(joinHash)
        .withCompactTable(compact)
        .withInlineCounter(inline)
        .withSlots(Const(slots))
        .withHash(joinHash)
        .withGather(!earlyMatTable)
        .withBlockBuild(blockBuild)
        .withBlockHash(false)
        .withPartition(partition=buildPartitioned, parallelPart=true)
        .withRightRenamed(rightRenamed = (if (blockBuild && buildPartitioned) Some(values) else None))
        .asIncomplete

    join = join
        .filter(postCond)
        .asIncomplete
        .rename('price -> Cast('l_extendedprice, lo.LoDouble()) * (DoubleConst(1.0) - 'l_discount))
        .aggregate(('price, PlusOp))
        .nestedSumDouble('price)

    for (i <- 1 to probeDepth)
      join = join.nestedSumDouble(UField(0))

    join
      .cast(UField(0), lo.LoFloat())
  }
}

object TpchQ19 {
  val funcType =
    Func(
      Map('lineitem -> TpchSchema.lineitem, 'part -> TpchSchema.part),
      (lo.LoFloat()))

  // Fields of `lineitem` used in the `postJoinCond`
  val postJoinFields: Seq[Id] = Seq('l_quantity, 'l_extendedprice, 'l_discount, 'l_partkey)

  // Fields of `part` used in the `postJoinCond`
  val postJoinPartFields: Seq[Id] = Seq('p_brand, 'p_container, 'p_size)

}


