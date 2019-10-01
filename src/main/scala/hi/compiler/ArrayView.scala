package ressort.hi.compiler
import ressort.lo._

/** Contains all the state needed to access the appropriate elements of a [[MetaArray]]
  *
  * Since each view corresponds to a particular loop nest's use of an underlying
  * array, so it is necessary to track for that loop all the offsets and lengths
  * that together constitute a single slice or sub-array.
  *
  * Also note that this array corresponds to one for loop, whose induction variable
  * may optionally be given as `cursor` (in the case of a [[ParallelView]]).
  * The sequenaial variant [[SequentialView]] does not permit arbitrary
  * (index-based) access to vectors, and instead requires that they be advanced through
  * one at a time.
  */
trait ArrayView {
  /** The [[MetaArray]] for which this is an accessor */
  def array: MetaArray

  /** The loop induction variable controlling travesal of this view's top level */
  def cursor: Option[SymLike]

  /** The cursor at the vector level of this array, if any */
  def vectorCursor: Option[SymLike] = this match {
    case n: NestedView => n.base.vectorCursor
    case _ => this.cursor
  }

  /** Is this an array view being used as part of an output? */
  def isOutput: Boolean

  /** Returns a stringified representation indented `indent` tabstops */
  def mkString(indent: Int=0): String = {
    val tabs = "  " * indent
    var str = s"$tabs$toString\n"
    this match {
      case f: FlatArray.View =>
      case d: DisjointBase.View =>
      case m: MultiArray.View => {
        str += m.head.mkString(indent+1)
        str += m.tail.map(_.mkString(indent+1)).mkString("")
      }
      case n: NestedView => {
        str += n.base.mkString(indent+1)
        str += n.ancillaries.map(_.mkString(indent+1)).mkString("")
      }
      case _ =>
    }
    str
  }

  /** Returns an appropriate loop over the current window of this array with given `body`,
    * and optional `cursor` replacing the bottom array's cursor if specified.
    */
  def windowLoop(body: LoAst, cursor: Option[SymLike]=None): LoAst = {
    val cur = cursor.getOrElse(vectorCursor.get)
    ForBlock(cur, maxCursor, body)
  }

  /** Any views corresponding to ancillaries in `array` */
  def ancillaries: List[ArrayView]

  /** Returns `LoRes` code for all definitions placed just _above_ this array's loop.
    *
    * If this array's cursor loop is embedded inside another, outer loop, then these
    * definitions will be private to each iteration of that outer loop.
    */
  def globalState: LoAst

  /** Returns `LoRes` code to set all local state as appropriate for the 0th loop iteration */
  def resetLocalState: LoAst

  /** Returns `LoRes` code to set all local state as appropriate for the last loop iteration */
  def endLocalState: LoAst

  /** Returns `LoRes` to set this array for the `n`th loop iteration, or `Nop` if it is sequential */
  final def getLocalState(n: Expr): LoAst = this match {
    case s: SequentialView => Nop
    case p: ParallelView => p.localState(n)
  }

  /** Returns `LoRes` code to increment this array for the next loop iteration, or `Nop` if it is parallel */
  final def getIncrementLocalState: LoAst = this match {
    case s: SequentialView => s.incrementLocalState
    case p: ParallelView => Nop
  }

  /** Returns an [[LValue]] for the `n`th element of the current vector slice */
  def access(n: Expr): LValue

  /** Returns an [[LValue]] for the `n`th element of the buffer at the bottom of this array view */
  def absolute(n: Expr): LValue

  final def apply(n: Expr) = access(n)

  /** A read-only access to the `n`th element of the current vector slice
    *
    * This is a hack needed to handle inline counters in [[ChunkArray]]'s, since the
    * correct source of a bucket's counter needs a [[Mux]], whbich is not an [[LValue]].
    * Only the [[OffsetsGenerator]] uses it, and it should be replaced as soon as
    * [[Mux]]  is made l-valuable, or some other solution is found.
    */
  def accessExpr(n: Expr): Expr = access(n)

  /** Returns an optional [[LValue]] for the `n`th element of the current mask's vector slice */
  def accessMask(n: Expr): Option[LValue]

  /** Returns an optional [[LValue]] for the `n`th element of the mask at the bottom o fthis array */
  def absoluteMask(n: Expr): Option[LValue]

  /** Returns an optional lvalue for the number of valid elements at the start of the current vector */
  def accessNumValid: Option[LValue]

  /** Number of elements accessible to one vector of this array level
    *
    * In general, this should be defined by dividing up the _logical_ vector length
    * ([[logVecLen]]) of this level's base if it is nested.
    */
  def physVecLen: Expr

  /** Number of non-padding elements in one vector of this array level
    *
    * This should generally be set by subtracting any padding added by this level
    * from this level's physical vector length ([[physVecLen]]).
    */
  def logVecLen: Expr

  /** Actual number of elements to process in an operator's main loop
    *
    * This uses any `numValid`, if present, to override [[logVecLen]].
    */
  def maxCursor: Expr

  /** Offset of the current vector at this level relative to the start of the deep base */
  def offset: Expr

  /** Number of sub-arrays into which this level divides its base, or 1 if it is flat */
  def numArrays: Expr

  // Common data-parallel operations to be filled in later
  def prefixSum(): LoAst = ???
  def rotRight(n: Expr): LoAst = ???
}

/** An [[ArrayView]] whose original [[MetaArray]] is indexable and accessible in parallel */
trait ParallelMacroView extends ArrayView { this: ArrayView =>
    /** Returns `LoRes` code to set up accesses to the `n`th sub-array of the [[MetaArray]]
    * from which this view derives, and includes this array's global state.
    *
    * Since some [[MetaArray]]s (i.e. the chunked array) will split into a multi-layered
    * view to make a nested loop, this method provides a way to set state of both to
    * correspond to the original array nesting level, as opposed to loop nest level.
    */
  def macroState(n: Expr): LoAst
}
  
/** A [[ArrayView]] whose sub arrays can be accessed arbitrarily and in parallel
  * 
  * If a view itself is parallel, than it is by definition part of a parallel macro array.
  */
trait ParallelView extends ParallelMacroView {
  /** Returns `LoRes` code for all state updates just _inside_ this array's `n`th loop */
  def localState(n: Expr): LoAst

  def resetLocalState: LoAst = localState(Const(0))

  def endLocalState: LoAst = localState(numArrays-1)

  def macroState(n: Expr): LoAst = globalState + localState(n)
}

/** A [[ArrayView]] whose individual sub-arrays must be visited one at a time */
trait SequentialView { this: ArrayView =>
  /** Returns `LoRes` code for all state updates just _inside_ this array's next loop iteration */
  def incrementLocalState: LoAst
}

/** An [[ArrayView]] with multiple levels */
trait NestedView extends ArrayView {
  /** The level below this one in the view */
  def base: ArrayView

  def array: NestedArray

  /** True iff this array's elements can be accessed in parallel */
  def parallel: Boolean = array.parallel

  def isOutput: Boolean = base.isOutput

  def numValid: Option[ArrayView]
}

/** A bundle of `LoRes` variables ([[SymLike]]s) that store state for a [[ArrayView]]
  *
  * These should all be safe to declare in [[ArrayView.declaration]]
  */
sealed trait ArrayViewState {
  /** All [[SymLike]]s contained in this [[ArrayViewState]] */
  def allIds = localIds ++ globalIds

  /** Any [[SymLike]]s to be defined locally (inside the array's loop) */
  def localIds: Seq[SymLike]

  /** Any [[SymLike]]s to be defined globally (above the array's loop) */
  def globalIds: Seq[SymLike]
}

trait NestedViewState {
  def index: SymLike
  def offset: SymLike
  def avgPhysVecLen: SymLike
  def physVecLen: SymLike
  def logVecLen: SymLike
  def remainder: SymLike
  def numArrays: SymLike
}

case class BasicNestedViewState(
    index: SymLike,
    offset: SymLike,
    avgPhysVecLen: SymLike,
    physVecLen: SymLike,
    logVecLen: SymLike,
    remainder: SymLike,
    numArrays: SymLike)
  extends NestedViewState {

  def localIds = Seq(offset, physVecLen, logVecLen)

  def globalIds = Seq(avgPhysVecLen, remainder, numArrays)
}

object NestedViewState {
  def apply(ids: TempIds): NestedViewState = {
    BasicNestedViewState(
      index = ids.newId("idx"),
      offset = ids.newId("off"),
      avgPhysVecLen = ids.newId("avg_len"),
      physVecLen = ids.newId("pvl"),
      logVecLen = ids.newId("lvl"),
      remainder = ids.newId("rem"),
      numArrays = ids.newId("narr"))
  }
}

case class ChunkViewState(
    chunk        : SymLike,
    chunkSize    : SymLike,
    count        : SymLike,
    maxSlot      : SymLike,
    curChunk     : SymLike,
    curArr       : SymLike,
    curMask      : SymLike,
    spilled      : SymLike,
    offset       : SymLike,
    avgPhysVecLen: SymLike,
    physVecLen   : SymLike,
    logVecLen    : SymLike,
    remainder    : SymLike,
    numArrays    : SymLike)
    extends NestedViewState {
  def index = chunk
  def localIds: Seq[SymLike] = Seq(count, maxSlot, curArr)
  def globalIds: Seq[SymLike] = Seq(chunk, chunkSize)
}

object ChunkViewState {
  def apply(ids: TempIds): ChunkViewState = {
    ChunkViewState(
      chunk = ids.newId("chunk"),
      chunkSize = ids.newId("chunk_sz"),
      count = ids.newId("count"),
      maxSlot = ids.newId("max_slot"),
      curChunk = ids.newId("cur"),
      curArr = ids.newId("arr"),
      curMask = ids.newId("mask"),
      spilled = ids.newId("spilled"),
      offset = ids.newId("off"),
      avgPhysVecLen = ids.newId("avg_len"),
      physVecLen = ids.newId("pvl"),
      logVecLen = ids.newId("lvl"),
      remainder = ids.newId("rem"),
      numArrays = ids.newId("narr"))
  }
}

case class DisjointSliceViewState(
    ptr: SymLike,
    ptrVecLen: SymLike,
    index: SymLike,
    offset: SymLike,
    ptrOffset: SymLike,
    avgPhysVecLen: SymLike,
    physVecLen: SymLike,
    logVecLen: SymLike,
    remainder: SymLike,
    numArrays: SymLike)
  extends NestedViewState {

  def localIds: Seq[SymLike] = Seq(ptr, index, offset, physVecLen, logVecLen)
  def globalState: Seq[SymLike] = Seq(ptrVecLen, avgPhysVecLen, remainder, numArrays)
}


object DisjointSliceViewState {
  def apply(ids: TempIds): DisjointSliceViewState = {
  DisjointSliceViewState(
      ptr = ids.newId("ptr"),
      ptrVecLen = ids.newId("ptr_vec_len"),
      index = ids.newId("idx"),
      offset = ids.newId("off"),
      ptrOffset = ids.newId("ptr_off"),
      avgPhysVecLen = ids.newId("avg_len"),
      physVecLen = ids.newId("pvl"),
      logVecLen = ids.newId("lvl"),
      remainder = ids.newId("rem"),
      numArrays = ids.newId("narr"))
  }
}

abstract class StatefulNestedView(state: NestedViewState) extends NestedView with ParallelView {
  def base: ArrayView

  def numValid: Option[ArrayView]

  def cursor: Option[SymLike]

  def access(n: Expr) = base.absolute(state.offset + n)

  def accessMask(n: Expr) = base.absoluteMask(state.offset + n)

  def absolute(n: Expr) = base.absolute(n)

  def absoluteMask(n: Expr) = base.absoluteMask(n)

  def physVecLen = state.physVecLen

  def logVecLen = state.logVecLen

  def maxCursor = numValid.map(_.access(state.index)).getOrElse(logVecLen)

  def offset = state.offset

  def numArrays = state.numArrays

  def accessNumValid = numValid.map(_.access(0))
}

/** An [[NestedView]] that merely forwards all non-overridden methods from `base` */
abstract class WrapperView(val orig: ArrayView) extends ArrayView {
  def isOutput: Boolean = orig.isOutput
  def array: MetaArray = orig.array
  def cursor: Option[SymLike] = orig.cursor
  def globalState = orig.globalState
  def access(n: Expr): LValue = ???
  def absolute(n: Expr): LValue = orig.absolute(n)
  def accessMask(n: Expr): Option[LValue] = orig.accessMask(n)
  def absoluteMask(n: Expr): Option[LValue] = orig.absoluteMask(n)
  def accessNumValid: Option[LValue] = orig.accessNumValid
  def ancillaries: List[ArrayView] = orig.ancillaries
  def physVecLen: Expr = orig.logVecLen
  def logVecLen: Expr = orig.physVecLen
  def maxCursor: Expr = orig.maxCursor
  def offset: Expr = orig.offset
  def numArrays: Expr = orig.numArrays
  override def endLocalState: LoAst = orig.endLocalState
  override def resetLocalState: LoAst = orig.resetLocalState
  override def windowLoop(body: LoAst, cursor: Option[SymLike]=None): LoAst = orig.windowLoop(body, cursor)
}
