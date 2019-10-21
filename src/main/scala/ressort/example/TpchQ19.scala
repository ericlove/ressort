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
          val l_extendedprice = tpch.l_extendedprice(i)
          val l_discount = tpch.l_discount((i))
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

  val litem = Concrete('lineitem_, TpchSchema.lineitem.s.fields.map(_.name.get.name).map(Id).toSet)
  val part = Concrete('part_, TpchSchema.part.s.fields.map(_.name.get.name).map(Id).toSet)

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
    extraHashBits: Option[Int]=Some(-3),
    slots: Expr = Const(4),
    buildPartitioned: Boolean=true,
    blockBuild: Boolean=false,
    earlyMat: Boolean=true,
    inline: Boolean=true,
    compact: Boolean=false
    ) extends TpchQ19(tpch) with Q19Auto {
  import ressort.hi.meta._
  import ressort.hi.meta.MetaParam._
  override val name = {
    val threadsStr = s"_${threads}t"
    val useHashStr = extraHashBits.map(_.toString.replace("-", "m")).map(n => s"_hash${n}eb").getOrElse("")
    val slotsStr = s"_${slots}s"
    val compactStr = if (compact) "_cpct" else ""
    val earlyMatStr = if (earlyMat) "_em" else ""
    val blockBuildStr = if (blockBuild) "_blockBuild" else ""
    val buildPartitionedStr = if (buildPartitioned) "_bpart" else ""
    val inlineStr = if (inline) "_inline" else ""
    s"q19nopa$threadsStr$useHashStr$slotsStr$compactStr$buildPartitionedStr$earlyMatStr$inlineStr$blockBuildStr"
  }

  val totalBits = new ParamList[Expr](List(Log2Up(Length('part))))
  val joinBits = new ExprParam(totalBits, e => e + Const(extraHashBits.getOrElse(0)))
  val joinHash = HashConfig(bits = joinBits)

  val meta = {
    var table: MetaOp = part
    if (threads > 1) table = table.splitPar(threads)
    if (earlyMat) table = table.rename()
    if (threads > 1) table = table.flatten

    var join: MetaOp = litem
      .withParams(totalBits)

    join = join
      .splitPar(threads)
      .filter(
        ('l_shipinstruct === TpchSchema.DELIVER_IN_PERSON),
        ('l_shipmode === TpchSchema.AIR || 'l_shipmode === TpchSchema.AIR_REG))
      .equiJoin(table, 'l_partkey,'p_partkey)
        .withHash(joinHash)
        .withCompactTable(compact)
        .withInlineCounter(inline)
        .withGather(!earlyMat)
        .withSlots(slots)
        .withBlockBuild(blockBuild)
        .withBlockHash(false)
        .withPartition(partition=buildPartitioned, threads=threads)

    join
      .filter(postCond)
      .rename('price -> Cast('l_extendedprice, lo.LoDouble()) * (DoubleConst(1.0) - 'l_discount))
      .aggregate(('price, PlusOp))
      .rename('price -> Cast('price, lo.LoFloat()))
      .connector(o => NestedSumFloat(o('price)))
  }

}

class TpchQ19AutoPartAll(
    val tpch: Option[TpchSchema.Generator],
    val partSize: Expr = Const(1 << 12),
    val partBits: Expr = Const(6),
    val threads: Int=16,
    val preThreads: Int=0,
    val postThreads: Int=0,
    val extraHashBits: Option[Int]=None,
    val slots: Int=1,
    val compact: Boolean=true,
    val earlyMatPart: Boolean=true,
    val earlyMat: Boolean=true,
    val buildPartitioned: Boolean=false,
    val blockBuild: Boolean=true,
    val twoSided: Boolean=true,
    val threadLocal: Boolean=true,
    val inline: Boolean=true)
  extends TpchQ19(tpch) with Q19Auto {


  val name = {
    val threadsStr = s"_${threads}t"
    val useHashStr = extraHashBits.map(_.toString.replace("-", "m")).map(n => s"_hash${n}eb").getOrElse("")
    val slotsStr = s"_${slots}s"
    val compactStr = if (compact) "_cpct" else ""
    val earlyMatPartStr = if (earlyMatPart) "_pem" else ""
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
    s"q19partall$threadsStr$useHashStr$nbitsStr$slotsStr$compactStr" +
      s"$buildPartitionedStr$earlyMatPartStr$earlyMatStr$inlineStr$twoSideStr" +
      s"$threadLocalStr$preThreadsStr$postThreadsStr"
  }

  import ressort.hi.meta._
  import ressort.hi.meta.MetaParam._
  val totalBits = new ParamList[Expr](List(Log2Up(partSize)))
  val joinBits = new ExprParam(totalBits, e => e - partBits)
  val joinMsb = new ExprParam(totalBits, e => e - partBits - Const(1))
  val partMsb = new ExprParam(totalBits, e => e - Const(1))
  val partHash = HashConfig(bits = partBits, msb = partMsb)
  val joinHash = HashConfig(bits = joinBits, msb = joinMsb)

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

    for (i <- 1 to probeDepth-1)
      table = table.shell

    table = table.splitPar(threads)
    table = table.rename()
    table = table.partition('p_partkey).withHash(partHash).withParallel(threads > 1)

    var join: MetaOp = litem.withParams(totalBits)

    join = join
      .splitSeq(preThreads)
      .splitPar(threads)
      .splitSeq(postThreads)
      .filter(
        ('l_shipinstruct === TpchSchema.DELIVER_IN_PERSON),
        ('l_shipmode === TpchSchema.AIR || 'l_shipmode === TpchSchema.AIR_REG))
      .rename()
      .partition('l_partkey)
        .withHash(partHash)
        .withParallel(threads > 1 && !threadLocal)
        .withGather(!earlyMat)

    join = join.shell

    join = join
      .equiJoin(table, 'l_partkey,'p_partkey)
        .withHash(joinHash)
        .withCompactTable(compact)
        .withInlineCounter(inline)
        .withSlots(Const(slots))
        .withHash(joinHash)
        .withGather(false)
        .withBlockBuild(blockBuild)
        .withBlockHash(false)
        .withPartition(partition=buildPartitioned, threads=threads)

    join = join
        .filter(postCond)
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

  def preJoinCond(o: Operator, crack: Boolean=false) = {
    if (crack) ???
    val inst = ('l_shipinstruct === TpchSchema.DELIVER_IN_PERSON)
    val mode = ('l_shipmode === TpchSchema.AIR || 'l_shipmode === TpchSchema.AIR_REG)
    if (crack) {
      Mask(o, o(inst))(mode)
    } else {
      o(inst && mode)
    }
  }

  def partHashBits(extraHashBits: Option[Int]=None) = {
    val len = Log2Up(Length('part))
    extraHashBits.map(Const(_) + len).getOrElse(len)
  }

  // Fields of `lineitem` used in the `postJoinCond`
  val postJoinFields: Seq[Id] = Seq('l_quantity, 'l_extendedprice, 'l_discount, 'l_partkey)

  // Fields of `part` used in the `postJoinCond`
  val postJoinPartFields: Seq[Id] = Seq('p_brand, 'p_container, 'p_size)

  def postJoinCond(joined: Operator) = {
    val smallContainer = {
      'p_container === SM_CASE  ||
      'p_container === SM_BOX   ||
      'p_container === SM_PACK  ||
      'p_container === SM_PKG
    }

    val medContainer = {
      'p_container === MED_BAG ||
      'p_container === MED_BOX ||
      'p_container === MED_PKG ||
      'p_container === MED_PACK
    }

    val largeContainer = {
      'p_container === LG_CASE  ||
      'p_container === LG_BOX   ||
      'p_container === LG_PACK  ||
      'p_container === LG_PKG
    }

    def size(max: Int): Expr = (Const(1) <= 'p_size && 'p_size <= Const(max))
    def qty(min: Int): Expr = ('l_quantity >= min && 'l_quantity <= min + 10)
    def bcond(brand: Const, cont: Expr, minQty: Int, maxSize: Int) = {
      Let(
        List(
          'brand := joined('p_brand === brand),
          'cont := joined(cont),
          'qty := joined(qty(minQty)),
          'size := joined(size(maxSize)),
          'z := Zip('brand, 'cont, 'qty, 'size)),
        in = 'z('brand && 'cont && 'qty && 'size))
    }

    val brand12 = ('p_brand === BRAND12 && smallContainer && qty(1) && size(5))
    val brand23 = ('p_brand === BRAND23 && medContainer && qty(10) && size(10))
    val brand34 = ('p_brand === BRAND34 && largeContainer && qty(20) && size(15))

    Let(
      List(
        'brand12 := bcond(BRAND12, smallContainer, 1, 5),
        'brand23 := bcond(BRAND23, medContainer, 10, 10),
        'brand34 := bcond(BRAND34, largeContainer, 20, 15),
        'z := Zip('brand12, 'brand23, 'brand34)),
    in = 'z('brand12 || 'brand23 || 'brand34))
  }


  def build(
      part: Operator='part.projectWithPosition('p_position),
      compact: Boolean=true,
      buckets: Expr = Length('part),
      slots: Expr = Const(1),
      inline: Boolean=true,
      hash: Operator=>Operator = p => p): Operator = {
    Let(
      List(
        'p := part,
        'ht := 
          HashTable(
            'p,
            hash = Some(hash('p('p_partkey))),
            buckets = Some(buckets),
            slots = Some(slots),
            inlineCounter = inline)
        ,
        'hist := (if (compact) Offsets('ht) else 'ht),
        'ht := (if (compact) Compact('ht, hist=Some('hist)) else 'ht)
      ),
      in = 'ht)
  }

  def buildPartitioned(
      part: Operator,
      slices: Expr,
      msb: Expr,
      lsb: Expr,
      hash: Operator=>Operator = p=>p,
      split: Boolean=false,
      threads: Int=1): Operator = {

    def partition(o: Operator, slices: Expr, getBits: Operator=>Operator, deep: Boolean): Operator = {
      Let(
        List(
          'p := o,
          'hash := getBits(hash('p('p_partkey))),
          'hist := Histogram(keys = 'hash, slices = slices),
          'hist := Offsets('hist, depth = (if (deep) 1 else 0)),
          'cat := Cat('hist, 'p),
          'p := Uncat('cat, 1),
          'hist := Uncat('cat, 0),
          'p :=
            Partition(
              keys = 'hash,
              values = 'p,
              hist = 'hist,
              parallel = deep),
          'values := Uncat('p, 0),
          'hist := Uncat('p, 1)),
        RestoreHistogram('values, if (deep) LastArray('hist) else 'hist))
    }

    val nbits = msb-lsb+1
    val lowBits = nbits/2
    val highBits = nbits - lowBits
    val first = 
      Let(
        List(
          'part_ := (if (threads > 1) SplitPar('part_, threads) else 'part_)),
        partition(
          part, 
          (if (split) Pow2(highBits) else slices),
          (o => o(BitRange(UField(0), msb, (if (split) nbits/2+lsb else lsb)))),
          deep = (threads > 1)))
    val second = 
      Let(
        List(
          'part_ := first),
        partition(
          'part_,
          Pow2(lowBits),
          o => o(BitRange(UField(0), lsb+nbits/2-1, lsb)),
          deep = true))
            
    if (split) second else first
  }

  def buildTable(
      threads: Int,
      buildPartitioned: Boolean,
      buildHashTable: Boolean,
      splitPartition: Boolean,
      earlyMat: Boolean,
      compact: Boolean,
      buckets: Expr,
      slots: Expr,
      slices: Expr=Const(0),
      msb: Expr=Const(0),
      lsb: Expr=Const(0),
      inline: Boolean=true,
      hash: Operator=>Operator): Operator = {
    Let(
      List(
        ('part_ := 'part),
        ('part_ := (if (threads > 1) Shell('part_) else 'part_)),
        ('table := Block({
          val part = if (earlyMat) {
              Let(
                List('p_partkey := 'part_('p_partkey)),
                Project(
                  'p_partkey,
                  'part_.project(TpchQ19.postJoinPartFields.map(f => f->f):_*)))
          } else {
              Let(
                List(
                  'p_partkey := 'part_('p_partkey),
                  'p_position := Position('part_)),
                Project('p_partkey, 'p_position))
          }
          if (buildPartitioned && !buildHashTable) {
            TpchQ19.buildPartitioned(part=part, threads=threads, slices=slices, msb=msb, lsb=lsb, hash=hash, split=splitPartition)
          } else if (buildPartitioned && buildHashTable) {
            val partitioned = 
              TpchQ19.buildPartitioned(part=part, threads=threads, slices=slices, msb=msb, lsb=lsb, hash=hash, split=splitPartition)
            TpchQ19.build(part=partitioned, buckets=buckets, hash=hash, compact=compact, slots=slots, inline=inline)
          } else {
            TpchQ19.build(part=part, buckets=buckets, hash=hash, compact=compact, slots=slots, inline=inline)
          }
        }, nonFusable=true))
    ),
  in = 'table)
  }
}


class TpchQ19Nopa(
    tpch: Option[TpchSchema.Generator],
    cat: Boolean=true,
    threads: Int=16,
    extraHashBits: Option[Int]=Some(-3),
    slots: Expr = Const(4),
    buildPartitioned: Boolean=true,
    earlyMat: Boolean=true,
    inline: Boolean=true,
    compact: Boolean=false
  ) extends TpchQ19(tpch) {

  val splitPartition:  Boolean=false

  val maxBit = TpchQ19.partHashBits(extraHashBits)
  val nbits = maxBit
  val slices = Pow2(nbits)
  val buckets = Pow2(maxBit)

  def hash(o: Operator): Operator = {
    if (extraHashBits.nonEmpty || buildPartitioned)
      Hash64(o, 64)(BitRange(UField(0), maxBit-1, 0))
    else
      o
  }
  def hashPartition(o: Operator): Operator = {
    hash(o)(BitRange(UField(0), nbits-1, 0))
  }

  def hashBuild(o: Operator): Operator = {
    hash(o)
  }

  val name = {
    val catStr = if (cat) "_cat" else ""
    val threadsStr = s"_${threads}t"
    val useHashStr = extraHashBits.map(_.toString.replace("-", "m")).map(n => s"_hash${n}eb").getOrElse("")
    val slotsStr = s"_${slots}s"
    val compactStr = if (compact) "_cpct" else ""
    val earlyMatStr = if (earlyMat) "_em" else ""
    val buildPartitionedStr = if (buildPartitioned) "_bpart" else ""
    val inlineStr = if (inline) "_inline" else ""
    s"q19nopa$catStr$threadsStr$useHashStr$slotsStr$compactStr$buildPartitionedStr$earlyMatStr$inlineStr"
  }
  println(s"$name: $nbits bits")

  val hiRes: Operator = 
    Let(
      Seq(
        ('table := 
            Let(
              List(
                ('part_ := 'part),
                ('part_ := {
                    if (threads > 1 && !buildPartitioned)
                      Shell('part_)
                    else if (threads > 1)
                      SplitPar(('part_), threads)
                    else
                      'part_
                  }),
                ('table := Block({
                    val part = if (earlyMat) {
                      Let(
                        List('p_partkey := 'part_('p_partkey)),
                        Project(
                          'p_partkey,
                          'part_.project(TpchQ19.postJoinPartFields.map(f => f->f):_*)))
                      } else {
                        Let(
                          List(
                            'p_partkey := 'part_('p_partkey),
                            'p_position := Position('part_)),
                          Project('p_partkey, 'p_position))
                      }
                      if (buildPartitioned) {
                        Let(
                          List(
                            'hist := Histogram(keys = hashPartition('part_('p_partkey)), slices = slices),
                            'hist := Offsets('hist, depth = (if (threads > 1) 1 else 0)),
                            'p := Cat('part_, 'hist),
                            'part_ := Uncat('p, 0),
                            'hist := Uncat('p, 1),
                            'p := part,
                            'p :=
                              Partition(
                                keys=hashPartition('part_('p_partkey)),
                                values='p, hist='hist, parallel = threads > 1),
                            'values := Uncat('p, 0),
                            'hist := Uncat('p, 1),
                            'p := RestoreHistogram('values, if (threads > 1) LastArray('hist) else 'hist)),
                          'p)
                      } else {
                        TpchQ19.build(part=part, buckets=buckets, hash=hash, compact=compact, slots=slots, inline=inline)
                      }
                    }, nonFusable=true))
                ),
              in = Block('table, nonFusable=true))),
        ('lineitem := (if (threads > 0) SplitPar('lineitem, threads) else 'lineitem)),
        ('lineitem := Shell('lineitem)),
        ('cat := (if (cat) Cat(('lineitem), 'table) else ('lineitem))),
        ('lineitem := Flatten(if (cat) (Uncat('cat, 0)) else 'lineitem)),
        ('table := (if (cat) Uncat('cat, 1) else 'table)),
        ('sel := Mask('lineitem, TpchQ19.preJoinCond('lineitem))),
        ('sel := 'sel.project(TpchQ19.postJoinFields.map(f => f->f):_*)),
        ('join :=
          Let(
            List(
              'join :=
                HashJoin(
                  left = 'sel,
                  right = 'table,
                  hash = hash('sel('l_partkey)),
                  test = Some(Equal('l_partkey, 'p_partkey)),
                  parallel = threads > 1)),
                'join
              //'hist := Offsets('join)),
              //(Flatten(Compact('join, hist=Some('hist))))
            )),
        ('join := {
            if (earlyMat) {
              'join
            } else {
              Project(
                'join,
                Gather('join('p_position), 'part).
                  project(TpchQ19.postJoinPartFields.map(f => f->f):_*))
            }
          }),
        ('price := (Eval(
          Mask('join, TpchQ19.postJoinCond('join)),
          Cast('l_extendedprice, lo.LoDouble()) * (DoubleConst(1.0) - 'l_discount)))),
        ('price := SumDouble('price)),
        ('price := NestedSumDouble('price))),
      in = 'price.cast(lo.LoFloat()))
}

class TpchQ19PartSingle(
    tpch: Option[TpchSchema.Generator],
    nbits: Expr,
    threads: Int=1,
    extraHashBits: Option[Int]=Some(0),
    slots: Int=1,
    compact: Boolean=false,
    earlyMatPart: Boolean=false,
    buildPartitioned: Boolean=true,
    inline: Boolean=true,
    disjoint: Boolean=true,
    blockLitem: Boolean=false)
  extends TpchQ19(tpch) {

  val name = {
    val bstr = if (blockLitem) "_litemblock" else ""
    val threadsStr = s"_${threads}t"
    val useHashStr = extraHashBits.map(_.toString.replace("-", "m")).map(n => s"_hash${n}eb").getOrElse("")
    val slotsStr = s"_${slots}s"
    val compactStr = if (compact) "_cpct" else ""
    val earlyMatPartStr = if (earlyMatPart) "_pem" else ""
    val buildPartitionedStr = if (buildPartitioned) "_bpart" else ""
    val inlineStr = if (inline) "_inline" else ""
    val nbitsStr = nbits match {
      case Const(n) => s"_nbits$n"
      case _ =>
    }
    s"q19part1$threadsStr$useHashStr$nbitsStr$slotsStr$compactStr$buildPartitionedStr$earlyMatPartStr$inlineStr$bstr"
  }
  val maxBit = TpchQ19.partHashBits(extraHashBits) - 1
  val slices = Pow2(nbits)
  val buckets = Pow2(maxBit - nbits + 1)

  def hash(o: Operator): Operator = {
    if (extraHashBits.nonEmpty || buildPartitioned)
      Hash64(o, 64)
    else
      o
  }

  def hashPartition(o: Operator): Operator = {
    hash(o)(BitRange(UField(0), nbits-1, 0))
  }

  def hashBuild(o: Operator): Operator = {
    hash(o)(BitRange(UField(0), maxBit-1, nbits))
  }

  val hiRes: Operator = {
    val partCol =
        Let(
          List(
            'block := (if (blockLitem) Block('litem) else 'litem),
            'litem := Mask('block, 'lcond),
            'l_partkey := 'litem('l_partkey)),
          'l_partkey.projectWithPosition('l_position))

    val litemPart = {
      Let(
        Seq(
          'litem := (if (threads > 1) SplitPar('lineitem, threads, disjoint=disjoint) else 'lineitem),
          'lcond := TpchQ19.preJoinCond('litem),
          'litem := Mask('litem, 'lcond),
          'hist := Histogram(keys = hashPartition('litem('l_partkey)), slices = slices),
          'hist := Offsets('hist, depth = (if (threads > 1) 1 else 0), disjoint=disjoint),
          'cat := Cat('litem, 'lcond, 'hist),
          'litem := Uncat('cat, 0),
          'lcond := Uncat('cat, 1),
          'hist := Uncat('cat, 2),
          'l_partkey := 'litem('l_partkey),
          'l_position := Position('litem),
          'p :=
            Partition(
              keys = hashPartition('l_partkey),
              values = Project('l_partkey, 'l_position),
              hist = 'hist,
              disjoint = disjoint,
              parallel = threads > 1),
          'values := Uncat('p, 0),
          'hist := Uncat('p, 1),
          'litem_part := RestoreHistogram('values, if (threads > 1) LastArray('hist) else 'hist)
        ),
        in = 'litem_part
      )
    }


    Let(
      Seq(
        ('ppart := 
          Let(
            List(
              ('part_ := 'part),
              ('part_ := {
                  if (threads > 1 && !buildPartitioned)
                    Shell('part_)
                  else if (threads > 1)
                    SplitPar('part_, threads, disjoint=disjoint)
                  else
                    'part_
                }),
              ('table := Block({
                  val part = if (earlyMatPart) {
                    Let(
                      List('p_partkey := 'part_('p_partkey)),
                      Project(
                        'p_partkey,
                        'part_.project(TpchQ19.postJoinPartFields.map(f => f->f):_*)))
                    } else {
                      Let(
                        List(
                          'p_partkey := 'part_('p_partkey),
                          'p_position := Position('part_)),
                        Project('p_partkey, 'p_position))
                    }
                    if (buildPartitioned) {
                      def localHash(o: Operator): Operator = hash(o)(BitRange(UField(0), maxBit, maxBit-nbits+1))
                      Let(
                        List(
                          'p := part,
                          'hist := Histogram(keys = hashPartition('part_('p_partkey)), slices = slices),
                          'hist := Offsets('hist, depth = (if (threads > 1) 1 else 0), disjoint=disjoint),
                          'p := Cat('part_, 'hist),
                          'part_ := Uncat('p, 0),
                          'hist := Uncat('p, 1),
                          'p := part,
                          'p := Partition(
                              keys=hashPartition('part_('p_partkey)),
                              values='p,
                              hist='hist,
                              parallel = threads > 1,
                              disjoint=disjoint),
                          'values := Uncat('p, 0),
                          'hist := Uncat('p, 1),
                          'p := RestoreHistogram('values, if (threads > 1) LastArray('hist) else 'hist),
                          'ht := 
                            HashTable(
                              'p,
                              hash = Some(hashBuild('p('p_partkey))),
                              buckets = Some(buckets),
                              slots = Some(slots),
                              inlineCounter = inline)
                          ,
                          'hist := (if (compact) Offsets('ht) else 'ht),
                          'ht := (if (compact) Compact('ht, hist=Some('hist)) else 'ht)),
                        'ht)
                    } else {
                      TpchQ19.build(part=part, buckets=buckets, hash=hash, compact=compact, slots=slots, inline=inline)
                    }
                  }, nonFusable=true))
              ),
            in = 'table)),
        ('lpart := Block(litemPart)),
        ('join :=
          Let(
            List(
              'join :=
                HashJoin(
                  left = 'lpart,
                  right = 'ppart,
                  hash = hashBuild('lpart('l_partkey)),
                  test = Some(Equal('l_partkey, 'p_partkey)),
                  parallel = buildPartitioned)
              ),
              in = 'join
              //,
              //'hist := Offsets('join)),
              //(Compact('join, hist=Some('hist)))
            )),
        ('join := {
            if (earlyMatPart) {
              'join
            } else {
              Project(
                'join,
                Gather('join('p_position), 'part).
                  project(TpchQ19.postJoinPartFields.map(f => f->f):_*))
            }
          }),
        ('lgat := Gather('join('l_position), 'lineitem)),
        ('lfields := Project('lgat.fields(TpchQ19.postJoinFields.filter(_ != Id('l_partkey.name)):_*))),
        ('zipped := Project('lfields, 'join)),
        ('price := (Eval(
          Mask('zipped, TpchQ19.postJoinCond('zipped)),
          Cast('l_extendedprice, lo.LoDouble()) * (DoubleConst(1.0) - 'l_discount))))
      ),
      in = (NestedSumDouble(SumDouble('price)).cast(lo.LoFloat())))
  }
}

class TpchQ19PartAll(
    tpch: Option[TpchSchema.Generator],
    nbits: Expr,
    threads: Int=8,
    extraHashBits: Option[Int]=None,
    slots: Int=1,
    compact: Boolean=true,
    earlyMatPart: Boolean=true,
    earlyMat: Boolean=true,
    buildPartitioned: Boolean=true,
    inline: Boolean=true)
  extends TpchQ19(tpch) {


  val name = {
    val threadsStr = s"_${threads}t"
    val useHashStr = extraHashBits.map(_.toString.replace("-", "m")).map(n => s"_hash${n}eb").getOrElse("")
    val slotsStr = s"_${slots}s"
    val compactStr = if (compact) "_cpct" else ""
    val earlyMatPartStr = if (earlyMatPart) "_pem" else ""
    val earlyMatStr = if (earlyMat) "_em" else ""
    val buildPartitionedStr = if (buildPartitioned) "_bpart" else ""
    val inlineStr = if (inline) "_inline" else ""
    val nbitsStr = nbits match {
      case Const(n) => s"_nbits$n"
      case _ =>
    }
    s"q19partall$threadsStr$useHashStr$nbitsStr$slotsStr$compactStr$buildPartitionedStr$earlyMatPartStr$earlyMatStr$inlineStr"
  }
  val maxBit = TpchQ19.partHashBits(extraHashBits) - 1
  val slices = Pow2(nbits)
  val buckets = Pow2(maxBit - nbits + 1)

  def hash(o: Operator): Operator = {
    if (extraHashBits.nonEmpty || buildPartitioned)
      Hash64(o, 64)
    else
      o
  }

  def hashPartition(o: Operator): Operator = {
    hash(o)(BitRange(UField(0), nbits-1, 0))
  }

  def hashBuild(o: Operator): Operator = {
    hash(o)(BitRange(UField(0), maxBit-1, nbits))
  }

  val hiRes: Operator = {
    val partCol =
        Let(
          List(
            'litem := Mask('litem, 'lcond),
            'l_partkey := 'litem('l_partkey)),
          'l_partkey.projectWithPosition('l_position))

    val litemPart = {
      Let(
        Seq(
          'litem := (if (threads > 1) SplitPar('lineitem, threads) else 'lineitem),
          'lcond := TpchQ19.preJoinCond('litem),
          'litem := Mask('litem, 'lcond),
          'hist := Histogram(keys = hashPartition('litem('l_partkey)), slices = slices),
          'hist := Offsets('hist, depth = (if (threads > 1) 1 else 0)),
          'cat := Cat('litem, 'lcond, 'hist),
          'litem := Uncat('cat, 0),
          'lcond := Uncat('cat, 1),
          'hist := Uncat('cat, 2),
          'l_partkey := 'litem('l_partkey),
          'l_position := Position('litem),
          'p :=
            Partition(
              keys = hashPartition('l_partkey),
              values = 'litem.project(TpchQ19.postJoinFields.map(f => f->f):_*),
              hist = 'hist,
              parallel = threads > 1),
          'values := Uncat('p, 0),
          'hist := Uncat('p, 1),
          'litem_part := RestoreHistogram('values, if (threads > 1) LastArray('hist) else 'hist)
        ),
        in = 'litem_part
      )
    }
      Let(
        Seq(
          ('ppart := 
            Let(
              List(
                ('part_ := 'part),
                ('part_ := {
                    if (threads > 1 && !buildPartitioned)
                      'part_
                    else if (threads > 1)
                      SplitPar('part_, threads)
                    else
                      'part_
                  }),
                ('table := Block({
                    val part = if (earlyMatPart) {
                      Let(
                        List('p_partkey := 'part_('p_partkey)),
                        Project(
                          'p_partkey,
                          'part_.project(TpchQ19.postJoinPartFields.map(f => f->f):_*)))
                      } else {
                        Let(
                          List(
                            'p_partkey := 'part_('p_partkey),
                            'p_position := Position('part_)),
                          Project('p_partkey, 'p_position))
                      }
                      if (buildPartitioned) {
                        Let(
                          List(
                            'hist := Histogram(keys = hashPartition('part_('p_partkey)), slices = slices),
                            'hist := Offsets('hist, depth = (if (threads > 1) 1 else 0)),
                            'p := Cat('part_, 'hist),
                            'part_ := Uncat('p, 0),
                            'hist := Uncat('p, 1),
                            'p := part,
                            'p :=
                              Partition(
                                keys=hashPartition('part_('p_partkey)),
                                values='p, hist='hist, parallel = threads > 1),
                            'values := Uncat('p, 0),
                            'hist := Uncat('p, 1),
                            'p := RestoreHistogram('values, if (threads > 1) LastArray('hist) else 'hist),
                            'ht := 
                            HashTable(
                              'p,
                              hash = Some(hashBuild('p('p_partkey))),
                              buckets = Some(buckets),
                              slots = Some(slots),
                              inlineCounter = inline)
                            ,
                            'hist := (if (compact) Offsets('ht) else 'ht),
                            'ht := (if (compact) Compact('ht, hist=Some('hist)) else 'ht)),
                          'ht)
                      } else {
                        TpchQ19.build(part=part, buckets=buckets, hash=hash, compact=compact, slots=slots, inline=inline)
                      }
                    }, nonFusable=true))
                ),
              in = 'table)),
            ('lpart := Block(litemPart)),
            ('join :=
              Let(
                List(
                  'join :=
                  HashJoin(
                    left = 'lpart,
                    right = 'ppart,
                    hash = hashBuild('lpart('l_partkey)),
                    test = Some(Equal('l_partkey, 'p_partkey)),
                    parallel = buildPartitioned),
                  'hist := Offsets('join)),
                (Compact('join, hist=Some('hist)))
              )),
            ('join := {
                if (earlyMatPart) {
                  'join
                } else {
                  Project(
                    'join,
                    Gather('join('p_position), 'part).
                    project(TpchQ19.postJoinPartFields.map(f => f->f):_*))
                }
              }),
            ('price := (Eval(
              Mask('join, TpchQ19.postJoinCond('join)),
              Cast('l_extendedprice, lo.LoDouble()) * (DoubleConst(1.0) - 'l_discount))))
          ),
        in = (NestedSumDouble(SumDouble('price)).cast(lo.LoFloat())))
    }

}
