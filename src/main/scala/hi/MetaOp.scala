// See LICENSE.txt
package ressort.hi.meta
import ressort.hi._
import ressort.lo
import scala.collection.mutable.{HashMap, HashSet, ArrayBuffer}

sealed trait MetaParam[T] {
  def concrete: ConcreteParam[T] = asInstanceOf[ConcreteParam[T]]

  def splat: Seq[ConcreteParam[T]]
}

object MetaParam {
  implicit def concParamFromValue[T](value: T): MetaParam[T] = new FixedParam[T](value)

  implicit def valueFromParam[T2, T <% T2](param: MetaParam[T])(implicit p: Program): T2 = {
    param match {
      case f: FixedParam[T] => 
        f.derivedFrom.map(p.setParam(_, f))
        f.value
      case c: ConcreteParam[T] => c.value
      case _ => println(param); println(p.params); ???
    }
  }
}

import MetaParam._

trait ConcreteParam[T] extends MetaParam[T] {
  def value(implicit p: Program): T

  def splat = Seq(this)
}

class FixedParam[T](var fixed: T, val derivedFrom: Option[MetaParam[_]]=None) extends ConcreteParam[T] {
  def value(implicit p: Program): T = fixed
}

class ExprParam(val from: MetaParam[Expr], val f: Expr=>Expr) extends MetaParam[Expr] {
  def splat: Seq[ConcreteParam[Expr]] = {
    for (par <- from.splat) yield {
      new ConcreteParam[Expr] {
        def value(implicit p: Program): Expr = {
          par match {
            case fixed: FixedParam[Expr] => f(fixed)
            case _ => f(par.value(p))
          }
        }
      }
    }
  }

  def +(o: Const): ExprParam = new ExprParam(this.from, ((e: Expr) => (f(e) + o)))
  def +(o: ExprParam): ExprParam = new ExprParam(this.from, ((e: Expr) => (f(e) + o.f(e))))
  def -(o: ExprParam): ExprParam = new ExprParam(this.from, ((e: Expr) => (f(e) - o.f(e))))
  def log2Up: ExprParam = new ExprParam(this.from, ((e: Expr) => Log2Up(f(e))))
}

class ParamList[T](values: List[T]) extends MetaParam[T] {
  def splat = values.map(new FixedParam[T](_, derivedFrom=Some(this)))

  override def toString: String = s"${super.toString}($values)"
}

/** Uniquely identifies a [[MetaOp]] */
class MetaOpId

sealed trait MetaOp {
  def generate(generator: MetaOp.Generator): Seq[MetaOp]

  def name: Option[ProgSym]

  def id: MetaOpId

  def inputs: Seq[MetaOp]
  def withInputs(inputs: Seq[MetaOp]): MetaOp

  def fields: Set[Id]

  def usedFields: Set[Id] = Set()

  def concrete(implicit p: Program): MetaOp

  /** Indicates that this operator removes or replaces masks, chunks, and other discontinuities */
  def completes: Boolean = false

  def rename(renames: (Id, Expr)*): Rename = Rename(this, renames)
  def addFields(fields: (Id, Expr)*): Rename = Rename(this, fields, keepInput=true)
  def equiJoin(right: MetaOp, lkey: Id, rkey: Id): EquiJoin = EquiJoin(this, right, lkey, rkey)
  def filter(conds: Expr*): Filter = Filter(this, conds.toSeq)
  def aggregate(aggregates: (Id, CommutativeOp)*): Aggregate = Aggregate(this, aggregates.toList)
  def groupBy(fields: Id*): Aggregate = Aggregate(this, aggregates=Nil, groupBy=fields)
  def partition(key: Id, renamed: Option[MetaOp=>MetaOp]=None): HashPartition = {
    HashPartition(this, key, renamed = renamed.map(f => f(this)))
  }
  def flatten: MetaOp = Connector(this, Flatten(_))
  def shell: MetaOp = Connector(this, Shell(_))
  def splitPar(slices: Expr) = slices match {
    case Const(n) if n < 2 => this
    case _ => Connector(this, SplitPar(_, slices))
  }
  def splitSeq(slices: Expr) = slices match {
    case Const(n) if n < 2 => this
    case _ => Connector(this, SplitSeq(_, slices))
  }
  def nestedSumDouble(expr: Expr, mute: Boolean=false) = {
    if (mute)
      this
    else
      this.connector(o => NestedSumDouble(o(expr)))
  }
  def cast(expr: Expr, t: Payload) = this.connector(o => o(Cast(expr, t)))

  def connector(f: Operator=>Operator): Connector = Connector(this, f)
  def compact: CompactMeta = CompactMeta(this)

  def asOperator(connector: Option[Operator=>Operator]=None): Operator = {
    connector match {
      case Some(f) => f(name.get)
      case _ => IdOp(name.get)
    }
  }

  def all: Seq[MetaOp] = {
    val gen = new MetaOp.Generator(this)
    gen.all
  }

  def allOps: Seq[Operator] = {
    val metaOps = this.all.map(_.pruneFields)
    for (o <- metaOps) yield {
      val p = new Program()
      p(o.concrete(p).name.get)
    }
  }


  /** Returns a new version of this operator where [[Rename]]s have been "pruned"
    * to output only those fields that are actually used
    */
  def pruneFields: MetaOp = {
    val usedFields = {
      val fmap = HashMap[MetaOpId, Set[Id]]()
      def walk(o: MetaOp, inUse: Set[Id]): Unit = {
        fmap(o.id) = fmap.getOrElse(o.id, Set()) ++ inUse.filter(o.fields.contains)
        val nextFields = o match {
          case r: Rename if r.keepInput => r.usedFields ++ r.in.fields.filter(inUse.contains(_))
          case r: Rename => r.usedFields
          case _ => o.usedFields ++ inUse
        }
        o.inputs.map(i => walk(i, nextFields))
      }
      walk(this, this.fields)
      fmap
    }

    def replace(o: MetaOp): MetaOp = {
      val newOp = o.withInputs(o.inputs.map(replace))
      newOp match {
        case r: Rename if r.renames.isEmpty =>
          r.copy(renames = usedFields(r.id).toSeq.map(f => f->f))
        case r: Rename =>
          r.copy(renames = r.renames.filter(p => usedFields(r.id).contains(p._1)))
        case j: EquiJoin =>
          j
        case _ => newOp
      }
    }

    replace(this)
  }
}

/** A [[MetaOp]] that requires compaction or reduction
  *
  * Some operations, like filtering, joins, and aggregation, produce by default results
  * that have invalid elements interspersed, or discontinuities of layout, which must be
  * resolved only if no "completing" operation intervenes: i.e. one that inherently
  * resolves such gaps by reduction or record movement.
  */
sealed trait NeedsCompletion { this: MetaOp =>
  def isComplete: Boolean
  def asComplete: MetaOp
  def asIncomplete: MetaOp
}

object MetaOp {
  class Generator(dag: MetaOp) {
    private val orig: HashMap[MetaOpId, MetaOp] = {
      val map = HashMap[MetaOpId, MetaOp]()
      def walk(o: MetaOp) {
        o.inputs.map(walk)
        map(o.id) = o
      }
      walk(dag)
      map
    }

    // Topologically sorted ordering of the nodes in `dag`, by ID
    private val ordered: Seq[MetaOpId] = {
      var list = List[MetaOpId]()
      val marked = HashSet[MetaOpId]()
      def walk(o: MetaOp) {
        o.inputs.map(walk)
        if (!marked.contains(o.id)) {
          list = o.id :: list
          marked += o.id
        }
      }
      walk(dag)
      list.reverse
    }

    private val combos = ArrayBuffer[MetaOp]()
    private val current = HashMap[MetaOpId, MetaOp]()

    def apply(op: MetaOp): MetaOp = current(op.id)

    private def generate(ordered: Seq[MetaOpId]): Unit = {
      if (ordered.isEmpty)
        return

      if (current.contains(ordered.head)) {
        println(s"Doubly-reached ${orig(ordered.head)}")
        return
      }

      for (o <- orig(ordered.head).generate(this)) yield {
        current(o.id) = o
        if (ordered.tail.isEmpty)
          combos += current(o.id)
        else
          generate(ordered.tail)
      }
    }

    lazy val all = {
      generate(ordered)
      current.clear()
      combos.toSeq
    }
  }
}


/** Chooses a hash function for [[EquiJoin]]s 
  *
  * @param msb The highest bit from which to extract key or hash values
  * @param bits The number of bits (including `msb`) to extract
  *
  * There are two special cases:
  * -- When `width` and `bits` are both zero (or `Const(0)`), there is one bucket
  *     (as used in nested-loops join)
  * -- When `width` is 0, __no__ hashing is performed, and the indicated bits are
  *     extracted directly from the key (as in an __array join__).
  */
case class HashConfig(
    width: MetaParam[Int] = 64,
    bits: MetaParam[Expr] = Const(10),
    msb: MetaParam[Expr] = Const(64)) {
  def splat: Seq[HashConfig] = {
    for {
      width <- width.splat
      bits <- bits.splat
      msb <- msb.splat
    } yield {
      HashConfig(width, bits, msb)
    }
  }

  def apply(o: Operator)(implicit p: Program): Operator = {
    val width: Int = this.width
    val bits: Expr = this.bits
    val extract: Expr = BitRange(UField(0), msb, msb-bits+1)
    (width, bits) match {
      case (0, Const(0)) => o(Const(0))
      case (0, _) => o(extract)
      case _ => Hash64(o, width)(extract)
    }
  }
}

case class Concrete(
    op: Operator,
    fields: Set[Id],
    params: Seq[MetaParam[_]]=Seq(),
    name: Option[ProgSym]=None,
    id: MetaOpId=new MetaOpId())
  extends MetaOp {

  def withInputs(inputs: Seq[MetaOp]): Concrete = this

  def concrete(implicit p: Program) = {
    val sym = p.fresh("concr")
    sym := op
    for (param <- params) {
      valueFromParam(param)
    }
    copy(name = Some(sym))
  }

  def withParams(params: MetaParam[_]*): Concrete = copy(params = params.toSeq)

  def inputs: Seq[MetaOp] = Seq()

  def generate(generator: MetaOp.Generator): Seq[MetaOp] = {
    val res = ArrayBuffer[MetaOp]()
    def helper(fixed: Seq[ConcreteParam[_]], remain: Seq[MetaParam[_]]): Unit = {
      if (remain.isEmpty) {
        res += copy(params = fixed)
      } else {
        val p = remain.head
        for (c <- p.splat) {
          helper(c +: fixed, remain.tail)
        }
      }
    }
    helper(Seq(), params)
    res.toSeq
  }
}

case class Connector(
    in: MetaOp,
    f: Operator => Operator,
    name: Option[ProgSym]=None,
    id: MetaOpId=new MetaOpId())
  extends MetaOp {

  def fields = in.fields

  def inputs: Seq[MetaOp] = Seq(in)

  def withInputs(inputs: Seq[MetaOp]): Connector = copy(in = inputs.head)

  def generate(generator: MetaOp.Generator): Seq[MetaOp] = {
    Seq(copy(in = generator(in)))
  }

  override def asOperator(connector: Option[Operator=>Operator]=None): Operator = {
    val f: Operator=>Operator = connector match {
      case Some(f2) => ((o: Operator) => f2(this.f(o)))
      case _ => this.f
    }
    in.asOperator(Some(f))
  }

  def concrete(implicit p: Program) = {
    val in = p.fresh("in")
    val ctor = p.fresh("ctor")
    in := this.in
    ctor := f(in)
    copy(in = in.metaOp.get, name = Some(ctor))
  }
}



case class HashPartition(
    in: MetaOp,
    key: Id,
    config: HashPartition.Config=HashPartition.Config(),
    renamed: Option[MetaOp]=None,
    name: Option[ProgSym]=None,
    id: MetaOpId=new MetaOpId())
  extends MetaOp {
  lazy val fields: Set[Id] = in.fields

  def inputs: Seq[MetaOp] = Seq(in) ++ renamed.toSeq

  def withInputs(inputs: Seq[MetaOp]): HashPartition = {
    copy(in = inputs.head, renamed = renamed.map(_ => inputs(1)))
  }

  override def usedFields: Set[Id] = Set(key)

  def generate(generator: MetaOp.Generator): Seq[MetaOp] = {
    for {
      c <- config.splat
    } yield {
      copy(in = generator(in), renamed = renamed.map(generator(_)), config = c)
    }
  }

  override def completes: Boolean = true

  def concrete(implicit p: Program) = {
    val in = p.fresh("in")
    val hist = p.fresh("hist")
    val part = p.fresh("hpart")
    val vals = p.fresh("vals")
    in := this.in
    hist := Histogram(config.hash(in(key)), slices = Pow2(config.hash.bits))
    hist := Offsets(hist, depth = (if (config.parallel) 1 else 0))
    if (config.block) {
      hist := Cat(in, hist)
      in := Uncat(hist, 0)
      hist := Uncat(hist, 1)
    }
    p.rename(this.in.id, in)
    this.renamed.map(in := _)
    val values: Operator = if (config.gather) {
      Project(in(key), Position(in))
    } else {
      in
    }
    part := Partition(keys = config.hash(in(key)), values = values, hist = hist, parallel = config.parallel)
    hist := Uncat(part, 1)
    part := Uncat(part, 0)
    if (config.parallel)
      hist := LastArray(hist)
    part := RestoreHistogram(part, hist)
    copy(in = in.metaOp.get, name = Some(part))
  }

  override def asOperator(connector: Option[Operator=>Operator]=None): Operator = {
    val base: Operator = connector match {
      case Some(f) => f(IdOp(name.get))
      case _ => IdOp(name.get)
    }
    if (config.gather.asInstanceOf[FixedParam[Boolean]].fixed)
      Gather(base(UField(1)), in.name.get)
    else
      base
  }

  def withHash(hash: HashConfig): HashPartition = copy(config = config.copy(hash = hash))
  def withBlock(block: MetaParam[Boolean]): HashPartition = copy(config = config.copy(block = block))
  def withRename: HashPartition = copy(renamed = Some(in.rename()))
  def withParallel(parallel: MetaParam[Boolean]): HashPartition = copy(config = config.copy(parallel = parallel))
  def withGather(gather: MetaParam[Boolean]): HashPartition = copy(config = config.copy(gather = gather))
}

object HashPartition {
  case class Config(
      hash: HashConfig = HashConfig(),
      gather: MetaParam[Boolean] = false,
      block: MetaParam[Boolean] = false,
      parallel: MetaParam[Boolean] = false) {
    def splat: Seq[Config] = {
      for {
        hash <- this.hash.splat
        gather <- this.gather.splat
        block <- this.block.splat
        parallel <- this.parallel.splat
      } yield {
        Config(hash = hash, block = block, parallel = parallel, gather = gather)
      }
    }
  }
}



case class EquiJoin(
    left: MetaOp,
    right: MetaOp,
    lkey: Id,
    rkey: Id,
    config: EquiJoin.Config=EquiJoin.Config(),
    isComplete: Boolean=true,
    name: Option[ProgSym]=None,
    id: MetaOpId=new MetaOpId())
  extends MetaOp with NeedsCompletion {
  lazy val fields: Set[Id] = left.fields ++ right.fields

  def inputs: Seq[MetaOp] = Seq(left, right)

  def withInputs(inputs: Seq[MetaOp]): EquiJoin = copy(left = inputs(0), right = inputs(1))

  override def usedFields: Set[Id] = Set(lkey, rkey)

  def asComplete: EquiJoin = copy(isComplete = true)
  def asIncomplete: EquiJoin = copy(isComplete = false)

  override def completes: Boolean = true

  def build(right: ProgSym)(implicit p: Program): Operator = {
    val parallel = config.threads > 1
    val split: Operator = if (parallel && config.partition) {
      SplitPar(right, Const(config.threads))
    } else {
      right
    }
    def rec(in: Operator): Operator = if (config.gather) {
      Let(
        List(
          rkey := in(rkey),
          'position := Position(in)),
        in = Project(IdOp(rkey), 'position))
    } else {
      in
    }
    if (config.partition) {
      val hist = p.fresh("hist")
      val part = p.fresh("jpart")
      val block = p.fresh("block")
      val in = p.fresh("in")
      in := split
      hist := Histogram(config.hash(in(rkey)), slices = Pow2(config.hash.bits))
      hist := Offsets(hist, depth = if (parallel) 1 else 0)
      if (config.blockBuild) {
        block := Cat(hist, in)
        hist := Uncat(block, 0)
        block := Uncat(block, 1)
      } else {
        block := in
      }
      part := Partition(config.hash(block(rkey)), rec(block), hist, parallel = parallel)
      hist := Uncat(part, 1)
      part := Uncat(part, 0)
      if (parallel)
        hist := LastArray(hist)
      RestoreHistogram(part, hist)
    } else {
      HashTable(
        rec(right), 
        hash = Some(config.hash(right(rkey))),
        buckets = Some(Pow2(config.hash.bits)),
        slots = Some(config.slots),
        inlineCounter = config.inlineCounter)
    }
  }

  def concrete(implicit p: Program) = {
    val left = p.fresh("left")
    val right = p.fresh("right")
    val table = p.fresh("htbl")
    val hash = p.fresh("hash")
    val join = p.fresh("join")
    val off = p.fresh("off")

    right := this.right
    left := this.left
    val newLeft = left.metaOp.get
    val newRight = right.metaOp.get
    table := build(right)
    if (config.compactTable && !config.partition)
      table := Compact(table, hist=Some(Offsets(table)))
    table := Block(table, nonFusable=true)
    if (config.blockHash) {
      left := Cat(left, table)
      table := Uncat(left, 1)
      left := Uncat(left, 0)
    }
    hash := config.hash(left(lkey))
    join := HashJoin(left, table, hash, test = Some(Equal(lkey, rkey)))
    if (isComplete) {
      off := Offsets(join)
      join := Compact(join, hist=Some(off))
    }
    copy(left = newLeft, right = newRight, name = Some(join))
  }

  override def asOperator(connector: Option[Operator=>Operator]=None): Operator = {
    val base = connector match {
      case Some(f) => f(name.get)
      case _ => IdOp(name.get)
    }
    if (config.gather.asInstanceOf[FixedParam[Boolean]].fixed) {
      val numLeft = left.fields.size
      Project(
        base.projFields(left.fields.filter(_ != lkey).toSeq:_*),
        Gather(
          base(UField(numLeft+1)),
          right.name.get))
    } else {
      base
    }
  }

  def generate(generator: MetaOp.Generator): Seq[MetaOp] = {
    for {
      config <- this.config.splat
    } yield {
      copy(left = generator(left), right = generator(right), config = config)
    }
  }

  def withPartition(
      partition: MetaParam[Boolean],
      threads: MetaParam[Int]=config.threads,
      split: MetaParam[Boolean]=config.split): EquiJoin = 
    copy(config = config.copy(partition=partition, threads=threads, split=split))
  def withGather(gather: MetaParam[Boolean]): EquiJoin = copy(config = config.copy(gather = gather))
  def withSlots(slots: MetaParam[Expr]): EquiJoin = copy(config = config.copy(slots = slots))
  def withInlineCounter(inlineCounter: MetaParam[Boolean]): EquiJoin = copy(config = config.copy(inlineCounter = inlineCounter))
  def withCompactTable(compactTable: MetaParam[Boolean]): EquiJoin = copy(config = config.copy(compactTable = compactTable))
  def withBlockHash(blockHash: MetaParam[Boolean]): EquiJoin = copy(config = config.copy(blockHash = blockHash))
  def withBlockBuild(blockBuild: MetaParam[Boolean]): EquiJoin = copy(config = config.copy(blockBuild = blockBuild))
  def withHash(hash: HashConfig): EquiJoin = {
    copy(config = config.copy(hash = hash))
  }
}

object EquiJoin {
  case class Config (
      hash: HashConfig=HashConfig(),
      slots: MetaParam[Expr] = Const(12),
      gather: MetaParam[Boolean] = true,
      inlineCounter: MetaParam[Boolean] = false,
      compactTable: MetaParam[Boolean] = false,
      partition: MetaParam[Boolean] = false,
      split: MetaParam[Boolean] = false,
      threads: MetaParam[Int] = 0,
      blockHash: MetaParam[Boolean] = true,
      blockBuild: MetaParam[Boolean] = true) {

    def splat: Seq[Config] = {
      for {
        hash <- this.hash.splat
        gather <- this.gather.splat
        inlineCounter <- this.inlineCounter.splat
        compactTable <- this.compactTable.splat
        blockHash <- this.blockHash.splat
        blockBuild <- this.blockBuild.splat
        partition <- this.partition.splat
        split <- this.split.splat
        threads <- this.threads.splat
      } yield {
        Config(
          hash = hash,
          slots=slots,
          gather=gather,
          inlineCounter=inlineCounter,
          compactTable=compactTable,
          blockHash=blockHash,
          blockBuild=blockBuild,
          partition=partition,
          split=split,
          threads=threads)
      }
    }
  }
}

case class Rename(
    in: MetaOp,
    renames: Seq[(Id, Expr)],
    keepInput: Boolean=false,
    name: Option[ProgSym]=None,
    id: MetaOpId=new MetaOpId())
  extends MetaOp {

  lazy val fields: Set[Id] = {
    var f = Set[Id]()
    if (keepInput) f ++= in.fields ++ renames.map(_._1).toSet
    if (renames.isEmpty) f ++= in.fields else f ++= renames.map(_._1).toSet
    f
  }

  def inputs: Seq[MetaOp] = Seq(in)

  def withInputs(inputs: Seq[MetaOp]): Rename = copy(in = inputs(0))

  override def usedFields: Set[Id] = {
    val res = renames.flatMap(_._2.ids).toSet
    res
  }

  def concrete(implicit p: Program): MetaOp = {
    val in = p.fresh("in")
    val ren = p.fresh("ren")
    in := this.in
    ren := hiRes(in)
    copy(in = in.metaOp.get, name = Some(ren))
  }

  private def hiRes(in: Operator)(implicit p: Program): Operator = {
    var assigns = List[Assign]()
    var renames = Seq[(Id, Expr)]()
    if (this.renames.isEmpty || keepInput)
      renames = this.in.fields.map(f => f->f).toSeq
    renames ++= this.renames
    for ((i, e) <- renames) {
      assigns ::= (i := in(e))
    }
    Let(assigns.reverse, in = Project(renames.map(p => IdOp(p._1)):_*))
  }

  def generate(generator: MetaOp.Generator): Seq[MetaOp] = {
    Seq(copy(in = generator(in)))
  }
}

case class Filter(
    in: MetaOp,
    conds: Seq[Expr],
    name: Option[ProgSym]=None,
    id: MetaOpId=new MetaOpId(),
    isComplete: Boolean=true,
    config: Filter.Config=Filter.Config())
  extends MetaOp with NeedsCompletion {

  def inputs: Seq[MetaOp] = Seq(in)

  def withInputs(inputs: Seq[MetaOp]): Filter = copy(in = inputs(0))

  def fields = in.fields

  override def usedFields: Set[Id] = conds.flatMap(_.ids).toSet

  def asComplete: Filter = copy(isComplete = true)
  def asIncomplete: Filter = copy(isComplete = false)

  def concrete(implicit p: Program) = {
    val in = p.fresh("in")
    val fil = p.fresh("fil")
    in := this.in
    if (config.cracked) {
      fil := in
      if (config.collect)
        fil := Position(fil, relative=true)
      for (c <- conds) {
        if (config.collect) {
          fil := Mask(fil, Gather(fil, in)(c))
          fil := Collect(fil)
        } else {
          fil := Mask(fil, fil(c))
        }
      }
      if (config.collect)
        fil := Gather(fil, in)
    } else {
      if (config.collect) {
        fil := Mask(in, in(conds.reduceLeft(And(_,_))))
        fil := Collect(fil)
      } else {
        fil := Mask(in, in(conds.reduceLeft(And(_,_))))
      }
    }
    if (isComplete)
      fil := Collect(fil)
    copy(name = Some(fil), in = in.metaOp.get)
  }

  def generate(generator: MetaOp.Generator): Seq[MetaOp] = {
    val in = generator(this.in)
    config.splat.map(c => copy(in = in, config = c))
  }

  def withCracked(cracked: MetaParam[Boolean]): Filter = copy(config = config.copy(cracked=cracked))
  def withCollect(collect: MetaParam[Boolean]): Filter = copy(config = config.copy(collect=collect))
}

object Filter {
  case class Config(
      val cracked: MetaParam[Boolean]=false,
      val collect: MetaParam[Boolean]=false,
      val gather: MetaParam[Boolean]=false) {
    def splat: Seq[Config] = {
      for {
        cracked <- this.cracked.splat
        collect <- this.collect.splat
      } yield {
        copy(cracked = cracked, collect = collect)
      }
    }
  }
}

case class Aggregate(
    in: MetaOp,
    aggregates: Seq[(Id, CommutativeOp)],
    groupBy: Seq[Id]=Nil,
    name: Option[ProgSym]=None,
    isComplete: Boolean=true,
    id: MetaOpId=new MetaOpId())
  extends MetaOp with NeedsCompletion {

  def inputs: Seq[MetaOp] = Seq(in)

  def withInputs(inputs: Seq[MetaOp]): Aggregate = copy(in = inputs(0))

  lazy val fields = aggregates.map(_._1).toSet

  override lazy val usedFields = fields.toSet ++ groupBy.toSet

  def asComplete: Aggregate = copy(isComplete = true)
  def asIncomplete: Aggregate = copy(isComplete = false)

  override def completes: Boolean = true


  def withAggregates(aggregates: (Id, CommutativeOp)*): Aggregate = {
    copy(aggregates = aggregates)
  }

  def concrete(implicit p: Program): Aggregate = {
    if (groupBy.nonEmpty) {
      concreteGroupBy(p)
    } else {
      concreteNoGroupBy(p)
    }
  }

  private def concreteGroupBy(implicit p: Program) = {
    val in = p.fresh("in")
    val agg = p.fresh("agg")
    in := this.in

    agg := HashTable(
      in,
      aggregates.map(a => NFieldName(a._1) -> a._2).toList)
    if (isComplete) {
      val off = p.fresh("off")
      off := Offsets(agg)
      agg := Compact(agg, hist=Some(off))
    }
    copy(in = in.metaOp.get, name = Some(agg))
  }

  private def concreteNoGroupBy(implicit p: Program) = {
    val in = p.fresh("in")
    val agg = p.fresh("agg")
    in := this.in

    val aggs = for ((s, o) <- aggregates) yield {
      val init = o match {
        case MinOp => None
        case MaxOp => None
        case _ => Some(DoubleConst(0.0))
      }
      (s := Reduce(in(s), o, init))
    }
    agg := Let(
      aggs.toList,
      in = Project(aggs.map(_.id).map(IdOp):_*))

    copy(in = in.metaOp.get, name = Some(agg))
  }

  def generate(generator: MetaOp.Generator): Seq[MetaOp] = {
    Seq(copy(in = generator(in)))
  }
}


case class CompactMeta(
    in: MetaOp,
    name: Option[ProgSym]=None,
    depth: Int=0,
    id: MetaOpId=new MetaOpId())
  extends MetaOp {

  def fields = in.fields

  def inputs: Seq[MetaOp] = Seq(in)

  def withInputs(inputs: Seq[MetaOp]): CompactMeta = copy(in = inputs(0))

  override def completes: Boolean = true

  def concrete(implicit p: Program) = {
    val in = p.fresh("in")
    val hist = p.fresh("hist")
    val comp = p.fresh("comp")

    in := this.in
    hist := Offsets(in, depth=depth)
    comp := Compact(in, hist=Some(hist))
    copy(in = in.metaOp.get, name = Some(comp))
  }

  def generate(generator: MetaOp.Generator): Seq[MetaOp] = {
    Seq(copy(in = generator(in)))
  }
}

