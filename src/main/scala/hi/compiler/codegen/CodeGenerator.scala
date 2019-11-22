// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi
import ressort.lo._
import ressort.compiler._

/** Holds one input our output to a generator instance */
sealed abstract class GeneratorIO(private val view: ArrayView) {
  def recType: Primitive = view.array.recType
}

/** Allows access to arbitrary indices in the current vector */
class IndexableIO(view: ArrayView) extends GeneratorIO(view) {
  def index(i: Expr): LValue = view.access(i)

  def indexMask(i: Expr): Option[Expr] = view.readMask(i)
}

/** This represents a strictly one-to-one relationship between the operator's
  * controlling cursor and indices into this array.
  */
class RecParallelIO(view: ArrayView, index: Expr) extends GeneratorIO(view) {
  def currentRec: LValue = view.access(index)

  def currentMask: Option[Expr] = view.readMask(index)

  def setMask(value: Expr): LoAst = view.setMask(index, value)

  def firstRec: LValue = view.access(Const(0))

  def zeroMask: Option[Expr] = view.readMask(Const(0))
}

/** A accessor whose cursor is advanced by the operator */
class StreamingIO(view: ArrayView, index: LValue) extends GeneratorIO(view) {
  def currentRec: LValue = view.access(index)

  def currentMask: Option[Expr] = view.readMask(index)

  def advanceRec: LoAst = (index := index + Const(1))
}

/** Generates code that processes LoRes arrays via a accessor interface.
  *
  * Each HiRes primitive operator has a corresponding code generator that
  */
trait CodeGenerator {
  /** String that identifies this generator and the algorithm it encodes */
  def generatorName: String
 
  /** Elaboration context for this generator */
  def elaboration: Elaboration
  
  /** LoRes symbol allocator that all code generation logic should use */
  lazy val tempIds = {
    class ExtendedTempIds(prefix: String) extends TempIds {
      override def newId(name: String): SymLike = {
        elaboration.tempIds.newId(prefix+"_"+name)
      }
    }
    new ExtendedTempIds(generatorName)
  }
  
  /** Returns an [[LoAst]] that performs some operation across all records in
    * this `ArrayView`'s current vector
    *
    * Many common stream processing tuning methods are implemented generically
    * here, including unrolling (with loads grouped separately from other code),
    * and software prefetcing.
    *
    * @param config Controls the degree of unrolling and prefetch
    *
    * @param process Function that returns an [[LoAst]] that implements the main
    *                 loop body, given an index (offset within current window)
    *                 as an [[Expr]] and a record as an [[LValue]].
    *
    * @param tempIds Local generator for temporary [[LoSym]]s
    */
  def processStream(view: ArrayView, config: RecStreamConfig, tempIds: TempIds)
                    (process: (Expr, LValue) => LoAst): LoAst = {
    val recs = for (n <- 0 until config.unroll) yield tempIds.newId("rec")
    lazy val rem = tempIds.newId("rem")
    val i = tempIds.newId("i")

    val decs = Block(recs map { Dec(_, view.array.recType) } toList)

    val prefs = for (n <- 0 until config.prefetch) yield {
      val base = i+config.unroll+config.prefetchOffset
      Prefetch(view.access(base + (n * config.prefetchStride)))
    }

    val fixup = if (config.unroll > 0) {
      val rec = tempIds.newId("rec")
      DecAssign(rem, Index(const=true), view.maxCursor % Const(config.unroll)) +
      Dec(rec, view.array.recType) +
      ForSeq(i, 0, rem, 1, 
        (rec := view.access(i)) +
        process(i, rec))
    } else {
      Nop
    }

    val body = if (config.unroll > 0) {
      val loads = for (n <- 0 until config.unroll) yield {
        (recs(n) := view.access(i+n))
      }
      val rest = for (n <- 0 until config.unroll) yield {
        (process((i+n), recs(n)))
      }
      Block(loads.toList ++ prefs.toList ++ rest.toList)
    } else {
      val rec = tempIds.newId("rec")
      Block(prefs.toList) +
      DecAssign(rec, view.array.recType, view.access(i)) +
      process(i, rec)
    }

    val (min, max, stride) = if (config.unroll > 0) {
      (rem, view.maxCursor - rem, config.unroll)
    } else {
      (Const(0), view.maxCursor, 1)
    }

    decs +
    fixup +
    ForSeq(
      index = i,
      min = min,
      max = max,
      stride = stride,
      body = body)
  }
}
