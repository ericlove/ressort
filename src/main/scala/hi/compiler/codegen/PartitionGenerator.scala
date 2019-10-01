package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._;
import ressort.hi

case class PartitionGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "partition"

  def emit(
      keys: ArrayView,
      values: ArrayView,
      hist: ArrayView,
      output: ArrayView,
      swwcb: Option[ArrayView],
      swwcbHist: Option[ArrayView],
      cursor: Expr,
      op: hi.Partition): LoopLevel = {
    val config = elaboration.config.rpart
    val (offs: ArrayView, sizes: Option[ArrayView]) = hist match {
      case m: MultiArray.View => (m.head, Some(m.tail.head))
      case o => (hist, None)
    }

    val ppi = {
      new PartitionProblemInstance(
        keys = keys,
        values = values,
        hist = offs,
        output = output,
        swwcb = swwcb,
        swwcbHist = swwcbHist,
        op,
        config = config,
        this)
    }

    val empty = if (config.useWriteBuffer) ppi.emptyBuffer else Nop

    val alloc = output match {
      case d: DisjointArray.View => {
        val s = sizes.get
        val i = elaboration.tempIds.newId("i")
        If (True,
          s.globalState +
          s.resetLocalState +
          ForBlock(i, s.maxCursor-1,
            HeapAlloc(d.absolutePointer(d.ptrOffset + i), s.access(i))))
      }
      case _ => Nop
    }

    LoopLevel(
      ppi.partition(cursor),
      initializer = Nop,
      higherInit = alloc,
      finalizer = empty)
  }
}

object PartitionGenerator {
  /** Returns the number of records per partition in a software
    * write-combining buffer used in partitioning.
    */
  def swwcbLength(lineSizeBytes: Int, recType: Primitive): Expr = {
    // TODO: Fix this to use static type sizing
    lineSizeBytes / Size(recType)
  }
}

class PartitionProblemInstance(
    val keys: ArrayView,
    val values: ArrayView,
    val hist: ArrayView,
    val output: ArrayView,
    val swwcb: Option[ArrayView],
    val swwcbHist: Option[ArrayView],
    val op: hi.Partition,
    val config: RadixPartConfig,
    val generator: PartitionGenerator)
  extends HistogramOperatorInstance {
  
  // Parameters to HistogramOperatorInstance
  val elaboration = generator.elaboration 
  val slices = output

  lazy val bufLen = PartitionGenerator.swwcbLength(config.linesz, values.array.recType)

  private def accessOutput(part: Expr, n: Expr): LValue = output match {
    case d: ArrayView with DisjointArray.View => d.access2d(part, n)
    case _ => output.access(n)
  }

  /** Generates an LoRes [[LoAst]] to move records to their output partitions
    * once the histogram has been built.
    *
    * Assumes that `prefixSum` has been called on the histogram array.
    */
  def partition(cursor: Expr): LoAst = {
    val part = elaboration.tempIds.newId("part")
    val i = elaboration.tempIds.newId("i")
    val outOff = elaboration.tempIds.newId("out_off")
    val bufOff = elaboration.tempIds.newId("pbuf_off")
    val bufCount = elaboration.tempIds.newId("pbuf_count")
    val histEnt = hist.access(part)
    val moveCode = {
      if (config.useWriteBuffer) {
        val buf = swwcb.get
        val shist = swwcbHist.get
        DecAssign(part, Index(const=true), keys.access(cursor)) +
        DecAssign(bufCount, Index(const=true), shist.access(part)) +
        DecAssign(bufOff, Index(const=true), part * bufLen) +
        Assign(buf.access(bufOff + bufCount), values.access(cursor)) +
        Increment(shist.access(part)) +
        If(Equal(bufCount, bufLen-1),
          DecAssign(outOff, Index(const=true), histEnt) +
          IPar(i, bufLen,
            (accessOutput(part, outOff + i) := buf.access(bufOff + i))) +
          Assign(histEnt, histEnt + bufLen) +
          Assign(shist.access(part), 0))
      } else {
        DecAssign(part, Index(const=true), keys.access(cursor)) +
        (accessOutput(part, hist.access(part)) := values.access(cursor)) +
        Increment(hist.access(part))
      }
    }
    printHist("Post Reduce:") + moveCode + printHist("Post Move") 
  }

  /** LoRes code to empty the reamining elements in each partition's buffer slot
    * after the whole input relation has been processed.
    */
  def emptyBuffer: LoAst = {
    val part = elaboration.tempIds.newId("part")
    val i = elaboration.tempIds.newId("i")
    val outOff = elaboration.tempIds.newId("out_off")
    val bufOff = elaboration.tempIds.newId("pbuf_off")
    val bufCount = elaboration.tempIds.newId("pbuf_count")
    val histEnt = hist.access(part)
    if (config.useWriteBuffer) {
      val buf = swwcb.get
      val shist = swwcbHist.get
      IPar(part, hist.maxCursor-1,
        (bufCount := (Index(true), shist.access(part))) +
        (bufOff := (Index(true), part * bufLen)) +
        (outOff := (Index(true), histEnt)) +
        ForBlock(i, bufCount,
          (accessOutput(part, outOff + i) := buf.access(bufOff + i))) +
        (histEnt := histEnt + bufCount))
    } else {
      Nop
    }
  }
}
