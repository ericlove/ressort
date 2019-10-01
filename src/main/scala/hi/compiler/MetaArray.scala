// See LICENSE.txt
package ressort.hi.compiler
import ressort.lo._


object MetaArray {
  val debugCycle = true
  val tempIds = new TempIds("_")
}


/** A contiguous array of record storage.
  *
  * This uniquely identifies an extent of memory that may be used by one or
  * more [[MetaArray]]s.
  *
  * @param length  Length of the array
  * @param numValid A variable to store the number of valid elements <= length, if it can change
  * @param initializer An optional function returning code to initialize an element
  *                    of this buffer given its [[LValue]].
  * @param finalizer An optional function returning code to deallocate an element
  *                  of this buffer given its [[LValue]].  It will be called for
  *                  each element in the destructor.
  * @param allocate     Should the allocator make a new buffer for this?
  * @param immaterial   If this buffer is allocated, allocate only a single
  *                     element for in-register use.
  * @param dynamicSize Indicates that this buffer's allocation must be scheduled based
  *                    on its size dependency, and that a new symbol must be declared
  *                    to hold its length.
  * @note A buffer is __not__ as case class; it is a unique object
  *       reference, unlike all other `HiArray` types.
  */
class Buffer(
    var name  : SymLike,
    var recType: Primitive,
    var length: Expr,
    var numValid: Option[SymLike] = None,
    var scalar: Boolean = false,
    var initializer: Option[LValue => LoAst] = None,
    var finalizer: Option[LValue => LoAst] = None,
    var allocate: Boolean = true,
    var immaterial: Boolean = false,
    var dynamicSize: Boolean = false,
    var mustMaterialize: Boolean = false) {

  def constructor: LoAst = {
    val decNv = declareNumValid
    lazy val i = MetaArray.tempIds.newId("i")
    if (allocate && !immaterial) {
      Dec(name, Ptr(Arr(recType))) +
          HeapAlloc(name, Some(length)) +
          initializer.map(init => ForBlock(i, length, init(Deref(name).sub(i)))).getOrElse(Nop) +
          decNv
    } else if (allocate && immaterial) {
      // Immaterialized arrays must be declared inside the loop where they are used!
      //
      // Otherwise, they would be declared at too high a scope, resulting in e.g. all
      // parallel loop iterations sharing a single copy, rather than the allocation of
      // thread-local storage, as is required.
      Nop
    } else {
      decNv
    }
  }

  def destructor: LoAst = {
    lazy val i = MetaArray.tempIds.newId("i")
    if (allocate && !immaterial) {
      finalizer.map(fin => ForBlock(i, length, fin(Deref(name).sub(i)))).getOrElse(Nop) +
          Free(name)
    } else if (allocate && immaterial) {
      finalizer.map(fin => fin(name)).getOrElse(Nop)
    } else {
      Nop
    }
  }

  def declareImmaterial: LoAst = {
    // Yes, this is a bit of a kludge: we set the "pointer" field
    // of an immaterial array to a non-pointer record type, and
    // the resulting accessor must handle it accordingly.
    if (allocate && immaterial) {
      val decNv = declareNumValid
      Dec(name, recType) + decNv + initializer.map(init => init(name)).getOrElse(Nop)
    } else {
      Nop
    }
  }

  private def declareNumValid: LoAst = {
    numValid.map(nv => DecAssign(nv, Index(), length)).getOrElse(Nop)
  }
}

object Buffer {
  def apply(recType: Primitive, length: Expr, name: SymLike): Buffer = {
    val numValid = MetaArray.tempIds.newId("nval")
    new Buffer(name, recType, length, Some(numValid))
  }
}


/** An array of records with nesting metadata attached.
  *
  * ==:Two Varieties:==
  * 1. - a '''flat''' array represents a flat array buffer of records or
  *       supporting data.
  * 2. - a '''nested''' array provides layers of structure on top of a base.
  */
sealed trait MetaArray {


  /** Returns a copy of this array with `mask` at its innermost level */
  def withMask(mask: Option[Buffer]): MetaArray

  /** Returns any mask present at the base of this array */
  def mask: Option[Buffer]

  /** The type of records contained in this array's buffer */
  def recType: Primitive = buffer.recType

  /** The buffer at the bottom of this array */
  def buffer: Buffer

  /** HiRes expression for the number of elements in the outermost level of
    * this array.
    */
  def length: Expr

  /** The number of elements to allocate in the buffer of an array cloned from this one */
  def cloneBufferLength: Expr

  /** HiRes expression for the number of times this array's base is subdivided
    * by the overall array.
    */
  def deepNumSlices: Expr

  /** The maximum number of records in the innermost array
    * that any sub-array of this structure might contain.
    */
  def maxWindowSize: Expr

  /** Replicates this array's structure on top of a new [[Buffer]] of given type
    *
    * @returns The clone of this array and a list of any new [[Buffer]]s to be allocated.
    * */
  def clone(
      name: SymLike,
      recType: Primitive = this.recType,
      length: Expr = this.cloneBufferLength): (MetaArray, List[Buffer])

  /** Returns a clone of that has no discontinuities */
  def cloneContiguous: (MetaArray, List[Buffer]) = {
    clone(MetaArray.tempIds.newId("clone"), recType = recType, length = length)
  }

  /** Returns a sliced [[MetaArray]] with the same number of levels as this but a new base, and allocated buffers.
    *
    * This is used where nesting must be preserved but the number of elements per slice
    * will necessarily be fixed, as in the case of a reduction (1 element per slice).
    */
  def cloneFixedLengthSlices(name: SymLike, recType: Primitive, length: Expr): (MetaArray, List[Buffer])

  /** Copies the deep structure of this `HiArray` with a reference to an
    * existing `HiArray` at the deepest level.
    *
    * Used by operators that do work in-place.
    */
  def cloneRef(): this.type = this

  /** List of supporting data structures used by this level */
  def ancillaries: List[MetaArray] = Nil

  /** Returns an array for an ancillary data structure based on this
    * array whose base can contain `numElements` records of type recType`.
    *
    * Wherever the main data structure is subdivided, so too is the ancillary,
    * the ancillary's subdivision is always accomplished using a mere
    * [[SlicedArray]], whereas the main array may be divided using a histogram
    * or other more complex structure.
    */
  def ancillary(recType: Primitive, length: Expr, name: SymLike): MetaArray

  /** Returns `Some(this)` iff this `HiArray` is a `HiResBuffer` */
  def asFlatArray: Option[FlatArray] =  None

  /** Returns `Some(this)` iff this `HiArray` is a `NestedHiArray` */
  def asNestedArray: Option[NestedArray] = None

  /** Returns a version of this structure with one layer of nesting removed,
    * or throws an exception if this is a flat array.
    */
  def flatten: MetaArray

  /** Returns a version of this structure with the `padding` field set as indicated */
  def withPadding(padding: Expr): MetaArray

  /** Returns a string representation of this structure for debugging */
  def mkString(indent: Int=1): String

  /** Returns a set of all [[Buffer]]s referenced in this array */
  def buffers(): Set[Buffer] = {
    Set(this.buffer) ++ ancillaries.flatMap(_.buffers())
  }

  /** Number of outer loop levels implied by this array (nesting depth) */
  def depth: Int = 0

  /** Code to allocate this array */
  def constructor: LoAst = Nop

  /** Code to deallocate this array */
  def destructor: LoAst = Nop

  /** Returns a new [[ArrayView]] with fresh state for a new traversal of this array */
  def view(cursors: Map[Int, SymLike], isOutput: Boolean): ArrayView

  /** A `LoRes` [[Struct]] type that contains all necessary information to use this array */
  def struct: Struct

  /** Returns `LoRes` code to assign this array to a lvalue of type `this.struct` */
  def assignToStruct(lv: LValue): LoAst
}

/** Only used to hold output arrays for multi-output fused nodes */
case class MultiArray(head: MetaArray, tail: MetaArray*) extends MetaArray {
  def array = head

  def buffer = head.buffer

  override def depth: Int = {
    // This is a hack to make [[Partition]]'s output have the "right" depth
    (head :: tail.toList).map(_.depth).max
  }

  override def ancillaries = tail.toList

  def withMask(mask: Option[Buffer]): MultiArray = {
    MultiArray(head = head.withMask(mask), tail = tail:_*)
  }

  def mask: Option[Buffer] = head.mask

  def mkString(indent: Int=1): String = {
    val tabs = "  "*indent
    val inner = {
      val h = head.mkString(indent+1)
      val t = tail.map(_.mkString(indent+1))
      t.foldLeft(h) { case (pre, post) => pre  + "\n" + post }
    }
    tabs + s"MultiHiArray(\n"  +
    inner + "\n" +
    tabs + ")"
  }

  def withPadding(padding: Expr): MultiArray = {
    MultiArray(head = head.withPadding(padding), tail = tail:_*)
  }

  def flatten: MultiArray = {
    MultiArray(head = head.flatten, tail = tail:_*)
  }

  def clone(
      name: SymLike,
      recType: Primitive = this.recType,
      length: Expr = this.cloneBufferLength): (MetaArray, List[Buffer]) = {
    val (newHead, allocs) = head.clone(name, recType, length)
    val arr = MultiArray(
        head = newHead,
        tail = tail.map(_.cloneRef()):_*)
    (arr, allocs)
  }

  override def buffers(): Set[Buffer] = {
    head.buffers ++ tail.map(_.buffers).flatten
  }

  def cloneFixedLengthSlices(name: SymLike, recType: Primitive, length: Expr): (MetaArray, List[Buffer]) = ???

  def struct: Struct = ???
  def assignToStruct(lv: LValue): LoAst = ???
  /** As seen from class MultiArray, the missing signatures are as follows.
    *  For convenience, these are usable as stub implementations.
    */
  def ancillary(recType: Primitive,length: Expr,name: SymLike): MetaArray = ???
  def cloneBufferLength: Expr = head.cloneBufferLength
  def deepNumSlices: Expr = head.deepNumSlices
  def length: Expr = head.length
  def maxWindowSize: Expr = head.maxWindowSize
  def view(cursors: Map[Int, SymLike], isOutput: Boolean): MultiArray.View = {
    MultiArray.View(
      this,
      head.view(cursors, isOutput),
      tail.map(_.view(cursors, isOutput)):_*)
  }
    
}

object MultiArray {
  case class View(array: MultiArray, head: ArrayView, tail: ArrayView*) extends ArrayView {
    override def toString: String = {
      s"MultiView(${array.buffer.name})"
    }
    def isOutput: Boolean = head.isOutput
    def cursor: Option[SymLike] = None
    def endLocalState: LoAst = ???
    def resetLocalState: LoAst = ???
    def globalState = ???
    def localState(n: Expr) = ???
    def access(n: Expr): LValue = ???
    def accessMask(n: Expr): Option[LValue] = None
    def absolute(n: Expr): LValue = ???
    def absoluteMask(n: Expr): Option[LValue] = None
    def accessNumValid: Option[LValue] = None
    def physVecLen: Expr = ???
    def logVecLen: Expr = ???
    def maxCursor: Expr = ???
    def numArrays: Expr = ???
    def offset: Expr = ???
    def ancillaries: List[ArrayView] = head :: tail.toList
  }
}

/** A flat meta-array with no nesting.
  *
  * @param buffer The physical [[Buffer]] to contain this array's elements
  * @param mask   A boolean-typed buffer to hold per-element predicate masks, if any
  * @param scalar  Set to true if this array actually holds one scalar element
  *                per window, as opposed to an array of length one.
  */
case class FlatArray(
    override val buffer: Buffer,
    mask: Option[Buffer] = None)
  extends MetaArray {

  def withMask(mask: Option[Buffer]): FlatArray = copy(mask = mask)

  def clone(
      name: SymLike,
      recType: Primitive = this.recType,
      length: Expr = this.cloneBufferLength): (MetaArray, List[Buffer]) = {
    val arr = copy(Buffer(recType, length, name))
    arr.buffer.scalar = buffer.scalar
    if (buffer.numValid.isEmpty)
      arr.buffer.numValid = None
    (arr, arr.buffer :: Nil)
  }

  def view(cursors: Map[Int, SymLike], isOutput: Boolean): FlatArray.View = {
    FlatArray.View(this, cursor = cursors.get(0), isOutput=isOutput)
  }

  def length: Expr = buffer.length

  def ancillary(recType: Primitive, length: Expr, name: SymLike): FlatArray = {
    val buffer = Buffer(recType, length, name)
    buffer.numValid = None
    FlatArray(buffer)
  }

  def cloneBufferLength = buffer.length

  def deepNumSlices = Const(1)

  def withPadding(padding: Expr): FlatArray = this

  override def buffers: Set[Buffer] = Set(buffer) ++ mask

  def flatten = throw new Error("Can't flatten a flat array: "+this)

  def maxWindowSize = length

  def mkString(indent: Int=1): String = {
    val tabs = "  "*indent
    val title = if (buffer.scalar) "FlatScalar" else "FlatVector"
    val immat = if (buffer.immaterial) ", IMMAT" else ""
    val alloc = if (buffer.allocate) ", ALLOC" else ""
    val must  = if (buffer.mustMaterialize) ", MUST" else ""
    var str = tabs
    str += s"""$title[${buffer.recType}$immat$alloc$must](${buffer.name}, len=${length})"""
    mask.map { m => str += s"\n$tabs  mask = \n${m}" }
    str
  }

  def cloneFixedLengthSlices(name: SymLike, recType: Primitive, length: Expr): (MetaArray, List[Buffer]) = clone(name, recType, length)

  def struct = {
    val fields = {
      val base = List(
        Id("arr") -> Ptr(Arr(buffer.recType)),
        Id("nval") -> Index())
      mask.map(m => base ++ Map(Id("mask") -> Ptr(Arr(m.recType)))).getOrElse(base)
    }
    Struct(
      name = Id(s"_lo_arr_${buffer.recType.mangledName}"),
      fields = fields)
  }

  def assignToStruct(lv: LValue): LoAst = {
    (lv.dot(Id("arr")) := buffer.name) +
        (lv.dot(Id("nval")) := buffer.numValid.getOrElse(buffer.length)) +
        (mask.map(m => (lv.dot('mask) := m.name))).getOrElse(Nop)
  }
}

object FlatArray {
  case class View(
        array: FlatArray,
        cursor: Option[SymLike]=None,
        isOutput: Boolean=false)
      extends ArrayView with ParallelView {
    override def toString: String = {
      s"FlatView[$cursor](${array.buffer.name}, length = ${array.length} ${array.mask.map(_.name)})"
    }
    def globalState = Nop
    def localState(n: Expr) = Nop
    def access(n: Expr): LValue = {
      if (array.buffer.immaterial) { array.buffer.name } else { Deref(array.buffer.name).sub(n) }
    }
    def accessMask(n: Expr): Option[LValue] = {
      array.mask.map { m =>
          if (m.immaterial)
            m.name
          else
            Deref(m.name).sub(n)
      }
    }
    def absolute(n: Expr): LValue = access(n)
    def absoluteMask(n: Expr): Option[LValue] = accessMask(n)
    def accessNumValid: Option[LValue] = if (array.buffer.scalar) None else array.buffer.numValid
    def physVecLen: Expr = array.buffer.length
    def logVecLen: Expr = array.buffer.length
    def maxCursor: Expr = array.buffer.numValid.getOrElse(array.buffer.length)
    def numArrays: Expr = Const(0)
    def offset: Expr = Const(0)
    def ancillaries: List[ArrayView] = Nil
  }
}


/** An array with multiple levels, corresponding to multiple loop iterations
  *
  * Each `NestedHiArray` has a base pointer, which indicates the
  * `HiArray` instance on top of which it builds additional structure,
  * and an ancillary array list, which contains all `HiArray`s that hold
  * supporting data, such as a histogram or range list.
  */
sealed abstract class NestedArray extends MetaArray {
  /** Base array on which this one provides additional structure */
  def base: MetaArray

  def buffer = base.buffer

  /** Returns a copy of this array with `base` replaced by the agrument */
  def withBase(base: MetaArray): NestedArray

  def withMask(mask: Option[Buffer]): NestedArray = withBase(base.withMask(mask))

  def mask: Option[Buffer] = base.mask

  /** Represents the number of valid elements in each slice of this accessor */
  def numValid: Option[MetaArray]

  /** Returns a copy of this array with `numValid` replaced by
    * the given argument.
    */
  def withSliceLengths(numValid: Option[MetaArray]): NestedArray

  /** Returns a copy of this array with `padding` set as indicated */
  def withPadding(padding: Expr): NestedArray

  override def asNestedArray = Some(this)

  override def depth = base.depth + 1

  /** True iff operations on this [[MetaArray]]'s sub-arrays are allowed to
    * execute in parallel.
    */
  def parallel: Boolean

  def flatten = base

  /** Number of elements per slice __in the base array__ to treat as i
    * invisible.
    */
  def padding(): Expr

  /** Amount to be added to `padding` in nested arrayss allocated as copies
    * of this one. This is needed for __in-place__ operators that raise the
    * degree of nesting.
    */
  def paddingToAdd(): Expr

  def cloneFixedLengthSlices(name: SymLike, recType: Primitive, length: Expr): (MetaArray, List[Buffer]) = {
    // For this clone method, "padding" is considered "padding to add", since the length
    // given is that of an innermost slice, and thus all padding needs to be reconstructed
    val newLength = length + ((padding + paddingToAdd) * this.length) 
    val (newBase, allocs) = base.cloneFixedLengthSlices(name, recType, newLength)
    val arr = SlicedArray(
      base          = newBase,
      slices        = this.length,
      parallel = parallel,
      padding       = padding + paddingToAdd,
      paddingToAdd  = Const(0))
    (arr, allocs)
  }

  def ancillary(recType: Primitive, length: Expr, name: SymLike): MetaArray = {
    def helper(array: MetaArray): MetaArray with DisjointArray = {
      array match {
        case n: NestedArray => DisjointSlice(helper(n.base), slices = n.length)
        case _ => {
          val buffer = Buffer(recType, length * deepNumSlices, name)
          val pointersName = MetaArray.tempIds.newId(s"${name.name}_pointers")
          val pointers = Buffer(Ptr(Arr(recType)), deepNumSlices, pointersName)
          val arr = DisjointBase(
            buffer = buffer,
            pointers = pointers, 
            slices = deepNumSlices)
          pointers.initializer = Some(arr.initPointers(_))
          buffer.allocate = false
          arr
        }
      }
    }
    helper(this)
  }

}


/** A nested array with only one element
  *
  * This aligns `base` with the loop iteration on level below this one.
  */
case class EmptyShellArray(base: MetaArray) extends NestedArray {
  def length = Const(1)

  def cloneBufferLength = base.cloneBufferLength

  def maxWindowSize = base.maxWindowSize

  override def ancillaries = List()

  def clone(
      name: SymLike,
      recType: Primitive = this.recType,
      length: Expr = this.cloneBufferLength): (MetaArray, List[Buffer]) = {
    val (newBase, allocs) = base.clone(name, recType, length)
    (copy(base = newBase), allocs)
  }

  def withBase(newBase: MetaArray) = {
    copy(newBase)
  }

  def withSliceLengths(numValid: Option[MetaArray]) = {
    SlicedArray(base, Const(1), false, numValid)
  }

  def numValid = None

  def padding(): Expr = Const(0)
  def paddingToAdd(): Expr = Const(0)
  def parallel = false
  def deepNumSlices = base.deepNumSlices

  override def ancillary(recType: Primitive, length: Expr, name: SymLike): MetaArray = {
    EmptyShellArray(base.ancillary(recType, length, name))
  }

  def mkString(indent: Int=1): String = {
    val tabs = "  "*indent
    tabs + s"EmptyShellHiArray[d$depth](" +
      tabs + s"  base           = \n"+base.mkString(indent+2) + "\n" +
      tabs + ")"
  }

  override def buffers(): Set[Buffer] = base.buffers

  def withPadding(padding: Expr): EmptyShellArray = this

  override def cloneFixedLengthSlices(name: SymLike, recType: Primitive, length: Expr): (MetaArray, List[Buffer]) = {
    // For this clone method, "padding" is considered "padding to add", since the length
    // given is that of an innermost slice, and thus all padding needs to be reconstructed
    val newLength = length + (padding * this.length) 
    val (newBase, allocs) = base.cloneFixedLengthSlices(name, recType, newLength)
    (copy(newBase), allocs)
  }

  def view(cursors: Map[Int, SymLike], isOutput: Boolean): ArrayView = {
    val baseView = base.view(cursors, isOutput)
    baseView match {
      case n: NestedView with ParallelMacroView => 
        EmptyShellArray.NestedParallelView(this, n, cursors.get(depth))
      case _ =>
        EmptyShellArray.FlatView(this, baseView, cursors.get(depth))
    }
  }

  def struct = base.struct

  def assignToStruct(lv: LValue) = base.assignToStruct(lv)
}

object EmptyShellArray {
  case class NestedParallelView(
      array: EmptyShellArray,
      base: NestedView with ParallelMacroView,
      cursor: Option[SymLike]) extends NestedView with ParallelView with ShellView {
    override def toString: String = {
      s"NestedShellView[$cursor]"
    }

    override def macroState(n: Expr): LoAst = base.macroState(n)

    def numValid: Option[ArrayView] = None
  }

  case class FlatView(
      array: EmptyShellArray,
      base: ArrayView,
      cursor: Option[SymLike]) extends NestedView with ParallelView with ShellView{
    override def toString: String = {
      s"FlatShellView[$cursor]"
    }

    def numValid: Option[ArrayView] = None

    override def macroState(n: Expr): LoAst = Nop

  }

  trait ShellView { this: NestedView with ParallelView =>

    def globalState = Nop

    def incrementLocalState = Nop

    def access(n: Expr): LValue = base.access(n)

    def absolute(n: Expr): LValue = base.absolute(n)

    def accessMask(n: Expr): Option[LValue] = base.accessMask(n)

    def absoluteMask(n: Expr): Option[LValue] = base.absoluteMask(n)

    def accessNumValid: Option[LValue] = None

    def ancillaries: List[ArrayView] = Nil

    def physVecLen: Expr = base.logVecLen

    def logVecLen: Expr = physVecLen

    def maxCursor: Expr = base.maxCursor

    def offset: Expr = base.offset

    def numArrays: Expr = Const(1)

    override def localState(n: Expr) = Nop

    override def endLocalState: LoAst = Nop

    override def resetLocalState: LoAst = Nop

    override def windowLoop(body: LoAst, cursor: Option[SymLike]=None): LoAst = {
      base.globalState +
      base.windowLoop(body, cursor)
    }
  }
}

/** Represents the division of an `HiArray` into a fixed number of slices
  * as defined by the [[Split]] operator.
  *
  * @param slices   Number of sub-arrays into which `base` is divided
  *
  * @param numValid An optional array of integers indicating, for each
  *                     slice, how many elements are valid (non-null).
  *                     All indices beyond the indicated length are considered
  *                     to be invalid, and subsequent arrays based on this one
  *                     omit them (in future implementations).
  */
case class SlicedArray(
    base:               MetaArray,
    slices:             Expr,
    parallel:           Boolean,
    numValid:           Option[MetaArray] = None,
    cloneDisjoint:      Boolean = false,
    padding:            Expr              = Const(0),
    paddingToAdd:       Expr              = Const(0))
  extends NestedArray {
  assert(slices != Const(0))

  def length = slices

  def cloneBufferLength = {
    base.cloneBufferLength + (if (cloneDisjoint) Const(0) else (paddingToAdd * slices))
  }

  def deepNumSlices = slices * base.deepNumSlices

  def maxWindowSize = base.maxWindowSize / slices

  override def ancillaries = List(numValid).flatten

  def clone(
      name: SymLike,
      recType: Primitive = this.recType,
      length: Expr = this.cloneBufferLength): (MetaArray, List[Buffer]) = {
    val (newBase, allocs) = base.clone(name, recType, length)
    val arr = this.copy(
      base          = newBase,
      numValid      = numValid map (_.cloneRef()),
      padding       = padding + paddingToAdd,
      paddingToAdd  = Const(0))
    if (cloneDisjoint) {
      DisjointArray.cloneFrom(arr, name = name, clearNumValid=false)
    } else {
      (arr, allocs)
    }
  }

  def withBase(newBase: MetaArray): SlicedArray = {
    copy(base = newBase)
  }

  def withSliceLengths(numValid: Option[MetaArray]): SlicedArray = {
    this.copy(numValid = numValid)
  }

  def mkString(indent: Int=1): String = {
    val tabs = "  "*indent
    var str = tabs
    str += s"SlicedArray[d$depth;slices=$slices,pad=$padding,+pad=$paddingToAdd,para=$parallel]\n"
    str += tabs + s"  base = \n"+base.mkString(indent+2) + "\n"
    numValid.map { nv =>
      str += tabs + s"  numValid =\n${nv.mkString(indent+2)}"
    }
    str
  }

  override def buffers(): Set[Buffer] =  base.buffers ++  numValid.map(_.buffer).toSet

  def withPadding(padding: Expr): SlicedArray = {
    this.copy(padding = padding,  paddingToAdd = Const(0))
  }

  def view(cursors: Map[Int, SymLike], isOutput: Boolean): SlicedArray.View = {
    SlicedArray.View(
      array = this,
      base = base.view(cursors, isOutput),
      numValid = numValid.map(_.view(cursors, isOutput)),
      state = NestedViewState(MetaArray.tempIds),
      cursor = cursors.get(depth)
    )
  }

  def struct: Struct = {
    val nvstruct = numValid.map(_.struct)
    val bstruct = base.struct
    val fields = {
      var base =
        List(
          Id(s"base") -> bstruct,
          Id(s"narr") -> Index())
      nvstruct.map(s => base ++= Map(Id("nval") -> s))
      base
    }
    Struct(
      name = Id(s"_sliced_${bstruct.mangledName}"),
      fields = fields)
  }

  def assignToStruct(lv: LValue): LoAst = {
    base.assignToStruct(lv.dot(Id("base"))) +
        (lv.dot(Id("narr")) := slices) +
        numValid.map(nv => nv.assignToStruct(lv.dot(Id("nval")))).getOrElse(Nop)
  }
}

object SlicedArray {
  case class View(
      array: SlicedArray,
      base: ArrayView,
      numValid: Option[ArrayView],
      state: NestedViewState,
      cursor: Option[SymLike]) extends StatefulNestedView(state) {

    override def toString: String = {
      s"SlicedView[$cursor](${state.offset}, slices = ${state.numArrays} = ${array.length}, ${state.logVecLen})"
    }

    def globalState = {
      (state.index := (Index(), Const(0))) +
          (state.numArrays := (Index(true), array.slices)) +
          (state.avgPhysVecLen := (Index(), base.logVecLen / state.numArrays)) +
          (state.remainder := (Index(), base.logVecLen % state.numArrays))
    }

    def localState(n: Expr) = {
      val offset = state.avgPhysVecLen * n
      (state.index := Safe(n)) +
          (state.physVecLen :=
              (Index(), Mux(n > 0, state.avgPhysVecLen, state.avgPhysVecLen + state.remainder))) +
          (state.logVecLen := (Index(), state.physVecLen - array.padding)) +
          (state.offset :=
              (Index(true),
                  base.offset +
                      Mux(n > 0, offset + state.remainder, offset)))
    }

    def incrementLocalState = {
      localState(state.index + 1)
    }

    def ancillaries: List[ArrayView] = numValid.toList
  }
}

sealed trait DisjointArray extends { this: MetaArray => 
  def clone(
      name: SymLike,
      recType: Primitive = this.recType,
      length: Expr = this.cloneBufferLength): (MetaArray with DisjointArray, List[Buffer])

  def view(cursors: Map[Int, SymLike], isOutput: Boolean): ArrayView with DisjointArray.View

  def mask: Option[Buffer]
}

object DisjointArray {
  trait View { this: ArrayView =>
    def absolutePointer(n: Expr): LValue

    def ptrVecLen: Expr

    def ptrOffset: Expr

    /** Returns an [[LValue]] referring to the `n`th element of the `part`th array */
    def access2d(part: Expr, n: Expr): LValue
  }

  def cloneFrom(
      array: MetaArray,
      name: SymLike,
      clearNumValid: Boolean=false,
      initPointersNull: Boolean=false
    ): (MetaArray with DisjointArray, List[Buffer]) = {
    def clearPadding(array: MetaArray): MetaArray = {
      array match {
        case n: NestedArray => {
          val length = n.buffer.length - (n.length * n.padding)
          val base = clearPadding(n.base).clone(name = name, length = length)._1
          n.withBase(base)
        }
        case _ => array
      }
    }
    val numPointers = array.deepNumSlices
    val immaterial = array.buffer.immaterial
    val mask = array.mask
    val buffer = Buffer(array.recType, array.buffer.length, name)
    def helper(array: MetaArray): (MetaArray with DisjointArray, List[Buffer]) = {
      array match {
        case n: NestedArray => {
          val numValid = (if (clearNumValid) None else n.numValid)
          val (base, buffers) = helper(n.base)
          (DisjointSlice(base, slices = n.length, numValid = numValid), buffers)
        }
        case _ => {
          val pointersName = MetaArray.tempIds.newId(s"${name.name}_pointers")
          val pointers = Buffer(Ptr(Arr(array.recType)), numPointers, pointersName)
          val arr = DisjointBase(
            buffer = buffer,
            pointers = pointers, 
            mask = mask,
            slices = numPointers,
            initPointersNull = initPointersNull)
          buffer.immaterial = immaterial
          pointers.immaterial = immaterial
          pointers.mustMaterialize = false
          pointers.initializer = Some(arr.initPointers(_))
          buffer.allocate = false
          (arr, buffer :: pointers :: Nil)
        }
      }
    }
    helper(clearPadding(array))
  }
}

case class DisjointSlice(
    base: MetaArray with DisjointArray,
    slices: Expr,
    numValid: Option[MetaArray]=None,
    allocFromNumValid: Boolean=false)
  extends NestedArray with DisjointArray {

  override def flatten = throw new Error(s"Can't flatten a disjoint array:\n${mkString(1)}")

  def length = slices

  def cloneBufferLength = base.cloneBufferLength

  def deepNumSlices = slices * base.deepNumSlices

  def maxWindowSize = base.maxWindowSize / slices

  def padding: Expr = Const(0)

  def paddingToAdd: Expr = Const(0)

  override def cloneContiguous: (MetaArray, List[Buffer]) = {
    val (newBase, allocs) = base.cloneContiguous
    val arr = SlicedArray(
      base = newBase,
      slices = slices,
      numValid = numValid,
      parallel = true)
    (arr, allocs)
  }

  override def ancillaries = numValid.toList

  def clone(
      name: SymLike,
      recType: Primitive = this.recType,
      length: Expr = this.cloneBufferLength): (DisjointSlice, List[Buffer]) = {
    val (newBase, allocs) = base.clone(name, recType, length)
    val arr = this.copy(
      base          = newBase,
      numValid      = numValid map (_.cloneRef()))
    (arr, allocs)
  }

  def withBase(newBase: MetaArray): DisjointSlice = {
    copy(base = newBase.asInstanceOf[MetaArray with DisjointArray])
  }

  def withSliceLengths(numValid: Option[MetaArray]): DisjointSlice = {
    this.copy(numValid = numValid)
  }

  def parallel = true

  def mkString(indent: Int=1): String = {
    val tabs = "  "*indent
    var str = tabs
    str += s"DisjointSlice[d$depth;slices=$slices](deep slice $deepNumSlices)\n"
    str += tabs + s"  base = \n"+base.mkString(indent+2) + "\n"
    numValid.map { nv =>
      str += tabs + s"  numValid =\n${nv.mkString(indent+2)}"
    }
    str
  }

  override def buffers(): Set[Buffer] =  base.buffers ++  numValid.map(_.buffer).toSet

  def withPadding(padding: Expr): DisjointSlice = {
    this
  }

  def view(cursors: Map[Int, SymLike], isOutput: Boolean): DisjointSlice.View = {
    DisjointSlice.View(
      array = this,
      base = base.view(cursors, isOutput),
      numValid = numValid.map(_.view(cursors, isOutput)),
      state = DisjointSliceViewState(MetaArray.tempIds),
      cursor = cursors.get(depth)
    )
  }

  def struct: Struct = {
    val nvstruct = numValid.map(_.struct)
    val bstruct = base.struct
    val fields = {
      var base =
        List(
          Id(s"base") -> bstruct,
          Id(s"narr") -> Index())
      nvstruct.map(s => base ++= Map(Id("nval") -> s))
      base
    }
    Struct(
      name = Id(s"_djsliced_${bstruct.mangledName}"),
      fields = fields)
  }

  def assignToStruct(lv: LValue): LoAst = {
    base.assignToStruct(lv.dot(Id("base"))) +
        (lv.dot(Id("narr")) := slices) +
        numValid.map(nv => nv.assignToStruct(lv.dot(Id("nval")))).getOrElse(Nop)
  }
}

object DisjointSlice {
  case class View(
      array: DisjointSlice,
      base: ArrayView with DisjointArray.View,
      numValid: Option[ArrayView],
      state: DisjointSliceViewState,
      cursor: Option[SymLike]) extends StatefulNestedView(state) with DisjointArray.View with ParallelView {

    override def toString: String = {
      s"DisjointSlicedView[$cursor](${state.offset}, slices = ${state.numArrays} = ${array.length} ${state.logVecLen})"
    }

    def globalState: LoAst = {
      (state.index := (Index(), Const(0))) +
          (state.numArrays := (Index(true), array.slices)) +
          (state.avgPhysVecLen := (Index(), base.logVecLen / state.numArrays)) +
          (state.ptrVecLen := (Index(), base.ptrVecLen / state.numArrays)) +
          (state.remainder := (Index(), base.logVecLen % state.numArrays))
    }

    def localState(n: Expr): LoAst = {
      val offset = state.avgPhysVecLen * n

      if (array.buffer.immaterial) {
        return (state.offset :=
              (Index(true),
                  base.offset + Mux(n > 0, offset + state.remainder, offset))) +
          (state.physVecLen :=
              (Index(), Mux(n > 0, state.avgPhysVecLen, state.avgPhysVecLen + state.remainder))) +
          (state.logVecLen := (Index(), state.physVecLen - array.padding))
      }

      val alloc = if (array.allocFromNumValid) {
        val ptr = base.absolutePointer(state.ptrOffset)
        If(Equal(ptr, Null),
          HeapAlloc(Deref(ptr), numValid.get.access(n)))
      } else {
        Nop
      }

      (state.index := Safe(n)) +
          (state.physVecLen :=
              (Index(), Mux(n > 0, state.avgPhysVecLen, state.avgPhysVecLen + state.remainder))) +
          (state.logVecLen := (Index(), state.physVecLen - array.padding)) +
          (state.offset :=
              (Index(true),
                  base.offset +
                      Mux(n > 0, offset + state.remainder, offset))) +
          (state.ptrOffset := (Index(true), base.ptrOffset + state.ptrVecLen * Safe(n))) +
          alloc +
          (state.ptr := (Ptr(Arr(array.recType)), base.absolutePointer(state.ptrOffset))) +
          (UseSym(absolutePointer(0).root, state.ptr))
    }

    def incrementLocalState = {
      localState(state.index + 1)
    }

    def ancillaries: List[ArrayView] = numValid.toList

    override def access(n: Expr) = {
      if (array.buffer.immaterial)
        array.buffer.name
      else
        Deref(state.ptr).sub(n)
    }

    override def accessMask(n: Expr) = base.absoluteMask(state.offset + n)

    override def absolute(n: Expr) = access(n)

    override def absoluteMask(n: Expr) = base.absoluteMask(n)

    def absolutePointer(n: Expr): LValue = base.absolutePointer(n)

    def ptrOffset = state.ptrOffset

    def ptrVecLen = state.ptrVecLen

    def access2d(part: Expr, n: Expr): LValue = {
      Deref(absolutePointer(base.ptrOffset + state.ptrVecLen * Safe(part))).sub(n)
    }
  }
}

case class DisjointBase(
    override val buffer: Buffer,
    pointers: Buffer,
    slices: Expr,
    mask: Option[Buffer]=None,
    initPointersNull: Boolean=false)
  extends MetaArray with DisjointArray {

  def withMask(mask: Option[Buffer]): DisjointBase = copy(mask = mask)

  def initPointers(rec: LValue): LoAst = {
    if (buffer.immaterial)
      return Nop

    if (initPointersNull)
      return (rec := Null)

    val i = MetaArray.tempIds.newId("i")
    val len = (buffer.length / slices) + (buffer.length % slices)
    HeapAlloc(rec, Some(len)) +
    buffer.initializer.map(init => ForBlock(i, len, init(Deref(rec).sub(i)))).getOrElse(Nop)
  }

  def ancillary(recType: Primitive, length: Expr, name: SymLike): MetaArray  = {
    FlatArray(buffer, mask).ancillary(recType, length, name)
  }

  override def buffers: Set[Buffer] = (buffer :: pointers :: mask.toList).toSet

  def clone(
      name: SymLike,
      recType: Primitive = this.recType,
      length: Expr = this.cloneBufferLength): (DisjointBase, List[Buffer]) = {
    val newBuffer = Buffer(recType, length, name)
    newBuffer.allocate = false
    val newPointers = Buffer(Ptr(Arr(recType)), slices, MetaArray.tempIds.newId("ptrs"))
    val arr =
      copy(
        buffer = newBuffer,
        pointers = newPointers)
    newPointers.initializer = Some(arr.initPointers(_))
    (arr, newBuffer :: arr.pointers :: Nil)
  }

  override def cloneContiguous: (MetaArray, List[Buffer]) = {
    val buf = Buffer(
        name = MetaArray.tempIds.newId("clone"),
        length = buffer.length,
        recType = buffer.recType)
    (FlatArray(buf), buf :: Nil)
  }
      

  def cloneBufferLength: Expr = length

  def cloneFixedLengthSlices(name: SymLike, recType: Primitive, length: Expr): (MetaArray, List[Buffer]) = {
    FlatArray(buffer, mask).clone(name, recType, length)
  }

  def deepNumSlices: Expr = Const(1)

  def flatten: MetaArray = throw new Error("Can't flatten a (disjoint) base array: " + this)

  def length: Expr = buffer.length

  def maxWindowSize: Expr = length

  def withPadding(padding: Expr) = this

  def assignToStruct(lv: LValue): LoAst = {
    (lv.dot('ptrs) := pointers.name) +
    mask.map(m => (lv.dot('mask) := m.name)).getOrElse(Nop)
  }

  def mkString(indent: Int): String = {
    val id = 'id
    val istr = buffer.initializer.map(i => s", init: ${i(id)}").getOrElse("")
    val immat = if (buffer.immaterial) " [IMMAT]" else ""
    val alloc = if (buffer.allocate) " [ALLOC]" else ""
    "  "*indent + s"DisjointBase(${buffer.name}$immat$alloc, ${pointers.name}, ${mask.map(_.name)}, len=$length$istr)"
  }

  def struct: Struct = {
    val fields = {
      val base = List(Id("ptrs") -> Ptr(Arr(pointers.recType)))
      mask.map(m => base ++ Map(Id("mask") -> Ptr(Arr(m.recType)))).getOrElse(base)
    }
    Struct(
      name = Id(s"_lo_djbase_${buffer.recType.mangledName}"),
      fields = fields)
  }

  def view(cursors: Map[Int, SymLike], isOutput: Boolean): DisjointBase.View = {
    DisjointBase.View(this, cursor = cursors.get(0), isOutput)
  }
}

object DisjointBase {
  case class View(
      array: DisjointBase,
      cursor: Option[SymLike]=None,
      isOutput: Boolean=false)
    extends ArrayView with ParallelView with DisjointArray.View {
    private def err = 
      throw new Error(s"Shouldn't be accessing a disjoint base array directly: "+this) 
    override def toString: String = {
      val id = 'none
      val istr = array.buffer.initializer.map(i => s", init: ${i(id)}").getOrElse("")
      s"DisjointBaseView[$cursor](${array.buffer.name}, length = ${array.length}$istr)"
    }
    def globalState = Nop
    def localState(n: Expr) = Nop
    def access(n: Expr): LValue = err
    def accessMask(n: Expr): Option[LValue] = array.mask.map { m =>
      if (m.immaterial)
        m.name
      else
        Deref(m.name).sub(n)
    }
    def absoluteMask(n: Expr): Option[LValue] = accessMask(n)
    def absolute(n: Expr): LValue = err
    def accessNumValid: Option[LValue] = if (array.buffer.scalar) None else array.buffer.numValid
    def physVecLen: Expr = array.buffer.length
    def logVecLen: Expr = array.buffer.length
    def maxCursor: Expr = array.buffer.numValid.getOrElse(array.buffer.length)
    def numArrays: Expr = Const(1)
    def offset: Expr = Const(0)
    def ancillaries: List[ArrayView] = Nil

    def absolutePointer(n: Expr): LValue = Deref(array.pointers.name).sub(n)

    def ptrOffset: Expr = Const(0)
    def ptrVecLen: Expr = array.pointers.length

    def access2d(part: Expr, n: Expr): LValue = {
      Deref(absolutePointer(part)).sub(n)
    }
  }
}

/** An array whose sub-arrays start at offsets specified in a histogram
  *
  * This array may result from partitioning, or from compacting a nested array with
  * variable-length sub-arrays.  An optional `numValid` may supply a second
  * histogram of counters indicating the number of still-valid elements within each
  * sub-array, starting from its offset.
  *
  * @param multi Set by [[MoveRecordsHist]] when that operator was
  *               multi-threaded, and this was its output.  Cleared whenever
  *               this array is copied.
  */
case class HistSlicedArray(
    base: MetaArray,
    hist: MetaArray,
    numValid: Option[MetaArray] = None,
    multi: Boolean = false,
    padding: Expr=Const(0),
    paddingToAdd: Expr=Const(0))
  extends NestedArray {

  // Subtract one to avoid counting extra histogram element as a slice
  def length = hist.maxWindowSize - Const(1)

  def cloneBufferLength = {
    base.cloneBufferLength + (paddingToAdd * length)
  }

  def deepNumSlices = {
    val res = length * hist.deepNumSlices
    res
  }

  override def ancillaries = List(Some(hist), numValid).flatten

  /** @note Variable-legnth slice array must be conservative in its window size
    *       estimate, as it cannot be known a priori how big each partition
    *       will turn out to be.
    */
  def maxWindowSize = base.maxWindowSize

  def clone(
      name: SymLike,
      recType: Primitive = this.recType,
      length: Expr = this.cloneBufferLength): (MetaArray, List[Buffer]) = {
    val (newBase, allocs) = base.clone(name, recType, length)
    val arr = this.copy(
      base = newBase,
      hist = hist.cloneRef(),
      numValid = None,
      multi = false) // cleared because only set by [[Partition]]
    (arr, allocs)
  }

  def withBase(newBase: MetaArray): HistSlicedArray = {
    copy(base = newBase)
  }

  def withSliceLengths(numValid: Option[MetaArray]): HistSlicedArray = {
    this.copy(numValid = numValid)
  }

  def withPadding(padding: Expr): HistSlicedArray = {
    this.copy(padding = padding,  paddingToAdd = Const(0))
  }

  def parallel = true

  def mkString(indent: Int=1): String = {
    val tabs = "  "*indent
    val hds = hist.mkString(indent+2)
    tabs + s"HistSlicedArray(\n"+
    tabs + "  padding = "+padding + "\n"                    +
    tabs + "  base    = \n"+base.mkString(indent+2) + "\n"  +
    tabs + "  hist    = \n"+hds + "\n"                      +
    numValid.map(nv => tabs + " numValid = \n"+nv.mkString(indent+2) +"\n").getOrElse("") +
    tabs + ")"
  }

  def view(cursors: Map[Int, SymLike], isOutput: Boolean): HistSlicedArray.View = {
    HistSlicedArray.View(
      array = this,
      base = base.view(cursors, isOutput),
      hist = hist.view(cursors, isOutput),
      numValid = numValid.map(_.view(cursors, isOutput)),
      state = NestedViewState(MetaArray.tempIds),
      cursor = cursors.get(depth)
    )
  }

  def struct: Struct = {
    val bstruct = base.struct
    val hstruct = hist.struct
    val nvstruct = numValid.map(_.struct)
    val fields = {
      var base =
        List(
          Id("base") -> bstruct,
          Id("hist") -> hstruct)
      nvstruct.map(s => base ++= Map(Id("nval") -> s))
      base
    }
    Struct(
      name = Id(s"_lo_histslice_${bstruct.mangledName}"),
      fields = fields)
  }

  def assignToStruct(lv: LValue): LoAst = {
    (base.assignToStruct(lv.dot(Id("base")))) +
        (hist.assignToStruct(lv.dot(Id("hist")))) +
        numValid.map(nv => nv.assignToStruct(lv.dot(Id("nval")))).getOrElse(Nop)
  }
}

object HistSlicedArray {
  case class View(
      array: HistSlicedArray,
      base: ArrayView,
      hist: ArrayView,
      numValid: Option[ArrayView],
      state: NestedViewState,
      cursor: Option[SymLike])
    extends StatefulNestedView(state) {

    override def toString: String = {
      s"HistSlicedView[$cursor](${state.logVecLen}, ${state.physVecLen}, {$state.offset})"
    }

    def globalState = {
      (state.index := (Index(), Const(0))) +
      (state.numArrays := (Index(true), hist.maxCursor - 1))
    }

    def localState(n: Expr) = {
      (state.index := Safe(n)) +
      (state.offset := (Index(true), base.offset + hist.access(n))) +
          (state.physVecLen := (Index(true), hist.access(n+1) - hist.access(n))) +
          (state.logVecLen := (Index(true), state.physVecLen - array.padding))
    }

    def ancillaries: List[ArrayView] = List(hist) ++ numValid

  }
}



/** A nested array with variable-length elements.
  *
  * This type is used both for hash tables and join results.  Each sub-array element is
  * called a __bucket__ and its variable number of elements are stored in __chunks__ of
  * allocated space, each with a fixed number of __slots__.
  *
  * Each bucket is given an initial range of slots (records) in a fixed-length, contiguous
  * base array, but if insertion exceeds this allocation, a new chunk with length `slots` is
  * dynamically allocated and appended to the bucket's linked list of chunk pointers.
  * If `disjoint` is set, however, even the initial allocations are in separate arrays.
  *
  * Semantically, a [[ChunkArray]] corresponds to one array-loop iteration, but under the hood
  * it expands to two loops: one for the original array, and another over the list of possible
  * chunks.  Therefore, it yields __two__ [[ArrayView]]s that result in these two loops:
  * an outer [[ChunkArray.ChunkView]] for thc chunk loop and an inner [[ChunkArray.View]]
  * over each sub-array.
  *
  * @param counts Index-typed counts of the number of used slots in each bucket
  * @param pointers A linked list of chunks for each bucket
  * @param inlineCounter Indicates the presence of an extra dummy slot at the start of 
  *                       each bucket to use for an inline counter.  The first field
  *                       of the record type must be an integer-valued type, and the
  *                       value of `slots` must be smaller than the log base 2 of its
  *                       bit width. 
  * @pararm alternateInlineCounts Alternate [[ChunkArray]] that contains the inline counters.
  *                           If empty, the this chunk array itself will be used.
  */
case class ChunkArray(
    base: MetaArray,
    counts: MetaArray,
    pointers: MetaArray,
    buckets: Expr,
    slots: Expr,
    inlineCounter: Boolean = false,
    disjoint: Boolean = false,
    alternateInlineCounts: Option[ChunkArray]=None)
  extends NestedArray {

  assert(
    !(inlineCounter && disjoint),
    s"ChunkArray can't be disjoint and also use inline counters")

  override def withPadding(padding: Expr): NestedArray = {
    ???
//    SlicedArray(
//      base = base.clone(MetaArray.tempIds.newId("buf")),
//      slices = buckets,
//      parallel = true,
//      numValid = Some(counts.cloneRef()),
//      padding = padding,
//      paddingToAdd = Const(0))
  }
  def mkString(indent: Int): String = {
    val tabs = "  " * indent
    tabs + s"ChunkArray(\n" +
    tabs + s"  base = \n${base.mkString(indent+2)}\n" +
    tabs + s"  counts = \n${counts.mkString(indent+2)}\n" +
    tabs + s"  pointers = \n${pointers.mkString(indent+2)}\n" +
    tabs + s"  alternateInlineCounts = ${alternateInlineCounts.map(_.buffer.name)}\n" +
    tabs + s"  buckets = $buckets ; slots $slots; disjoint = $disjoint\n"
  }
  def clone(
      name: SymLike,
      recType: Primitive = this.recType,
      length: Expr = this.cloneBufferLength): (MetaArray, List[Buffer]) = {
    val ptrName = MetaArray.tempIds.newId("ptrs")
    val (newBase, baseAllocs) = base.clone(name, recType, length)
    val (newPointers, pointerAllocs) =
      pointers.clone(ptrName, recType = ChunkArray.bucketRec(LoType(recType).toData, mask.nonEmpty))
    val arr = copy(
      base = newBase,
      counts = counts.cloneRef(),
      pointers = newPointers,
      alternateInlineCounts = Some(alternateInlineCounts.getOrElse(this)))
    newPointers.buffer.initializer = Some(arr.initPointerStruct)
    newPointers.buffer.finalizer = Some(arr.freePointerStruct)
    newBase.buffer.initializer = Some(arr.initDummyCounter)
    (arr, baseAllocs ++ pointerAllocs)
  }
  def cloneBufferLength: Expr = base.cloneBufferLength
  def deepNumSlices: Expr = buckets * base.deepNumSlices
  override def ancillaries = List(counts, pointers)
  def maxWindowSize: Expr = slots
  def length: Expr = buckets
  override def buffers(): Set[Buffer] = base.buffers ++ counts.buffers ++ pointers.buffers
  def numValid: Option[MetaArray] = Some(counts)
  def padding(): Expr = Const(0)
  def paddingToAdd(): Expr = Const(0)
  def parallel: Boolean = true
  def withBase(newBase   : MetaArray): ChunkArray = copy(base = newBase)
  def withSliceLengths(numValid: Option[MetaArray]): ChunkArray = copy(counts = numValid.getOrElse(counts))
  override def withMask(mask: Option[Buffer]): ChunkArray = copy(base = base.withMask(mask))

  def view(cursors: Map[Int, SymLike], isOutput: Boolean): ChunkArray.ChunkView = {
    val hashView =
      ChunkArray.View(
        array = this,
        base = base.view(cursors, isOutput),
        counts = counts.view(cursors, isOutput).asInstanceOf[ArrayView with ParallelView],
        pointers = pointers.view(cursors, isOutput).asInstanceOf[ArrayView with ParallelView],
        state = NestedViewState(MetaArray.tempIds),
        cursor = cursors.get(depth)
      )
    ChunkArray.ChunkView(
      array = this,
      base = hashView,
      state = ChunkViewState(MetaArray.tempIds),
      inlineCounterBase = alternateInlineCounts.map(_.view(cursors, isOutput).base).getOrElse(hashView),
      // Depth -1 is specially reserved for the chunk cursor so that all chunk nodes in
      // a fused DAG will be aligned.
      cursor = Some(cursors(-1))
    )
  }

  val bucketRec = ChunkArray.bucketRec(recType, mask.nonEmpty)
  val chunkStruct = ChunkArray.chunkStruct(recType, mask.nonEmpty)

  /** Returns a [[LoAst]] to initalize an element of the `pointers` buffer
    *
    * The [[OutputArrayGenerator]] sets this function as the buffer's initializer
    *
    * @param rec An [[LValue]] containing a record of the `ChunkArray.bucketRec` type
    */
  def initPointerStruct(rec: LValue): LoAst = {
    if (!buffer.immaterial) {
      (rec.dot('list) := Null) +
      (rec.dot('end) := Null)
    } else {
      Nop
    }
  }

  def freePointerStruct(rec: LValue): LoAst = {
    if (pointers.buffer.allocate && !buffer.immaterial) {
//      val j = LoSym(new SymId("j"))
//      val next = LoSym(new SymId("next"))
//      val cur = LoSym(new SymId("cur"))
//      (next := (Ptr(rec), rec.dash('list))) +
//          (cur := (Ptr(rec), rec.dash('list))) +
//          ForBlock(j, (Deref(counts.buffer.name).sub(i) + chunkSize - 1) / chunkSize,
//            (next := cur.dash('next)) +
//                (Free(cur)) +
//                (cur := next)))
      // For now, don't free..
     Nop
    } else {
      Nop
    }
  }

  /** Returns a [[LoAst]] to intialize the counter of a bucket's dummy element */
  def initDummyCounter(rec: LValue): LoAst = {
    if (inlineCounter) {
      buffer.recType match {
        case r: Record => UField(rec, 0) := Const(0)
        case _ => (rec := Const(0))
      }
    } else {
      Nop
    }
  }

  def assignToStruct(lv: LValue): LoAst = ???
  def struct: Struct = ???
}

object ChunkArray {

  /** Array view for a [[ChunkArray]]
    *
    * @note This view will be returned __inside__ a [[ChunkView]], which manages the linked
    *       list of chunks for each bucket.
    */
  case class View(
      array: ChunkArray,
      base: ArrayView,
      counts: ArrayView with ParallelView,
      pointers: ArrayView with ParallelView,
      state: NestedViewState,
      cursor: Option[SymLike])
    extends NestedView with ParallelView {

    override def toString: String = {
      s"ChunkArrayView[$cursor](${state.offset}, ${state.numArrays} = ${array.buckets}, ${state.physVecLen}, ${state.logVecLen}, ...)"
    }

    val bucketRec = array.bucketRec
    val chunkStruct = array.chunkStruct

    def numValid = Some(counts)

    def globalState: LoAst = {
      if (array.buffer.immaterial)
        return Nop

      // `state.remainder` should never be used because a HashArray's base will
      // always be allocated with enough space `slots` elements in each bucket
      // (See relevant code in the `OutputArrayGenerator`).
      (state.numArrays := (Index(true), array.buckets)) +
          (state.physVecLen := (Index(true), base.logVecLen / state.numArrays)) +
          (state.logVecLen := (Index(true), state.physVecLen - array.padding))
    }

    def localState(n: Expr): LoAst  = {
      if (array.buffer.immaterial)
        return Nop

      (state.offset := (Index(true), base.offset + (state.physVecLen * n))) +
      (state.index := (Index(true), Safe(n)))
    }

    def accessNumValid = None

    def access(n: Expr): LValue = {
      // Shouldn't be called directly, since ChunkView should always intervene
      ???
    }

    def absolute(n: Expr): LValue = ???

    def accessMask(n: Expr): Option[LValue] = ???
    def absoluteMask(n: Expr): Option[LValue] = ???

    def logVecLen: Expr = state.logVecLen
    def maxCursor: Expr = state.logVecLen
    def numArrays: Expr = state.numArrays
    def offset: Expr = state.offset
    def physVecLen: Expr = state.physVecLen
    def ancillaries = List(counts, pointers)
  }

  case class ChunkView(
      array: ChunkArray,
      base: ChunkArray.View,
      state: ChunkViewState,
      cursor: Option[SymLike],
      inlineCounterBase: ChunkArray.View)
    extends NestedView with SequentialView with ParallelMacroView {

    override def toString: String = {
      s"ChunkView[$cursor](${state.offset}, ${state.numArrays}, ${state.maxSlot})"
    }

    val inlineCounter = array.inlineCounter
    val slots = array.slots
    val disjoint = array.disjoint



    override def parallel = false
    val numValid: Option[ArrayView] = {
      val myBase = this.base
      // This unique ArrayView is created specifically so we can define an `accessExpr`
      // method that uses the inline counters for buckets that didn't spill.
      val numValidNonOpt = new WrapperView(base.counts) {
        override def accessExpr(n: Expr): Expr = {
          val dummy = {
            val vlen = 
              (inlineCounterBase.base.physVecLen / inlineCounterBase.array.length)
            val d = myBase.base.access(n * vlen)
            myBase.array.buffer.recType match {
              case r: Record => UField(d, 0)
              case _ => d
            }
          }
          if (inlineCounter)
            Mux(dummy <= slots, dummy, myBase.counts.access(n))
          else
            myBase.counts.access(n)
        }
      }
      Some(numValidNonOpt)
    }

    // Note: this relies on the fact that the size of the array cannot shrink without
    // a corresponding re-materialization of the inline counters into a new buffer
    def dummyCounter: LValue = {
      val dummy = Deref(inlineCounterBase.array.buffer.name).sub(inlineCounterBase.state.offset)
      inlineCounterBase.array.buffer.recType match {
        case r: Record => UField(dummy, 0)
        case _ => dummy
      }
    }

    def spilled: Expr = if (disjoint) True else state.spilled
    def bucket: LValue = base.pointers.access(base.state.index)

    /** Specializes an expression based on whether using an inline counter or not (or spilled) */
    def inline(ifInline: Expr, ifChunk: Expr): Expr = {
      if (array.inlineCounter)
        Mux(spilled, ifChunk, ifInline)
      else
        ifChunk
    }

    def firstChunkFull: Expr = {
      if (array.inlineCounter) 
        Mux(spilled, True, (dummyCounter >= array.slots))
      else
        state.count >= array.slots
    }

    def globalState: LoAst = {
      if (array.buffer.immaterial)
        return Nop

      val dummy = if (array.inlineCounter) Const(1) else Const(0)
      val setSpilled = if (disjoint) {
        DecAssign(state.spilled, Bool(true), True)
      } else if (array.inlineCounter) {
        DecAssign(state.spilled, Bool(), dummyCounter > array.slots)
      } else {
        DecAssign(state.spilled, Bool(), base.counts.access(base.state.index) > array.slots)
      }
      (state.chunk := (Index(), Const(0))) +
          (state.chunkSize := (Index(true), array.slots)) +
          (state.offset := (Index(), (if (disjoint) Const(0) else base.offset + dummy))) +
          (state.avgPhysVecLen := (Index(true), state.chunkSize)) +
          (state.physVecLen := (Index(true), state.chunkSize)) +
          (state.remainder := (Index(true), Const(0))) +
          setSpilled +
          (state.count := (Index(), inline(Const(0), base.counts.access(base.state.index)))) +
          (state.numArrays := (Index(), 1)) +
          (state.curChunk := (Ptr(base.chunkStruct), (if (disjoint) bucket.dot('list) else Null))) +
          (state.curArr := (Ptr(Arr(array.recType)), {
                if (disjoint)
                  state.curChunk.dot('arr)
                else
                  array.buffer.name
              })) +
          UseSym(array.buffer.name, state.curArr) +
          (if (array.mask.nonEmpty) {
            (state.curMask := (Ptr(Arr(Bool())), {
                  if (disjoint)
                    state.curChunk.dot('mask)
                  else
                    array.mask.get.name
                })) +
            UseSym(array.mask.get.name, state.curMask)
          } else {
            Nop
          }) +
          (state.maxSlot := (Index(), maxSlotMux)) +
          (state.logVecLen := (Index(), state.maxSlot))
    }

    def ancillaries: List[ArrayView] = List(inlineCounterBase)

    private val maxSlotMux: Expr = {
      val baseMux = 
        Mux(
          Equal(state.curChunk, bucket.dot('end)),
          Mux(state.count > state.chunkSize, 1 + ((state.count-1) % state.chunkSize), state.count),
          state.chunkSize)
      inline(dummyCounter, baseMux)
    }

    def macroState(n: Expr): LoAst = {
      base.globalState + base.localState(n) + globalState + resetLocalState
    }

    def incrementLocalState: LoAst  = {
      if (array.buffer.immaterial)
        return Nop

      val advance = {
        (state.curChunk := {
            if (disjoint)
              Deref(state.curChunk).dot('next)
            else
              Mux(Equal(state.curChunk, Null),
                bucket.dot('list),
                Deref(state.curChunk).dot('next))
            }) +
          postIncrement
      }
      val allocNext = {
        if (isOutput)
          If(((1+state.chunk) * state.chunkSize < state.count), allocChunk + postIncrement)
        else
          Nop
      }
      val res = {
        IfElse(
            Equal(bucket.dot('list), Null) || {
              if (disjoint)
                False
              else
                (Not(Equal(state.curChunk, Null)) && Equal(state.curChunk.dash('next), Null))
            },
          allocNext,
          advance)
      }
      res
    }

    def endLocalState: LoAst = {
      if (array.buffer.immaterial)
        return Nop

      ???
      (state.curChunk := bucket.dot('end)) +
          (state.count := inline(dummyCounter, base.counts.access(base.state.offset))) + // TODO: FIX?
          (state.chunk := state.count % state.chunkSize) +
          (state.curArr := Mux(spilled, Deref(state.curChunk).dot('buf), array.buffer.name)) +
          array
            .mask
            .map(m =>
              (state.curMask :=
                Mux(spilled, Deref(state.curChunk).dot('mask), m.name)))
            .getOrElse(Nop) +
          (state.numArrays := Mux(state.count > 0, (state.count + state.chunkSize - 1) / state.chunkSize, 1)) +
          (state.maxSlot := (Index(), maxSlotMux)) +
          (state.logVecLen := (Index(), state.maxSlot)) +
          (state.offset := Const(0))
    }


    private def postIncrement: LoAst = {
      (state.curArr := state.curChunk.dash('buf)) +
          array.mask.map(m => (state.curMask := state.curChunk.dash('mask))).getOrElse(Nop) +
          (state.chunk := state.chunk + 1) +
          (state.maxSlot := maxSlotMux) +
          (state.logVecLen := state.maxSlot) +
          (state.offset := Const(0))
    }

    /** Returns code to advance the chunk pointer only if another chunk is already allocated.
      *
      * The [[HashTableGenerator]] calls this to perform probes.
      */
    def nonAllocIncrement: LoAst = {
      if (array.buffer.immaterial)
        return Nop
      If(state.chunk + 1 < state.numArrays,
        (state.curChunk :=
          Mux(Equal(state.curChunk, Null),
            bucket.dot('list),
            Deref(state.curChunk).dot('next))) +
        postIncrement)
    }

    private def allocChunk: LoAst = {
      val end = bucket.dot('end)
      IfElse(Equal(bucket.dot('list), Null),
        {
          HeapAlloc(bucket.dot('list)) +
          (end := bucket.dot('list))
        },
        {
          HeapAlloc(end.dash('next)) +
            (end := end.dash('next))
        }) +
      (state.curChunk  := bucket.dot('end)) +
      (HeapAlloc(end.dash('buf), Some(state.chunkSize))) +
      (end.dash('next) := Null) +
      (state.spilled := True) +
      (state.numArrays := state.numArrays + 1)
    }

    def resetLocalState: LoAst = {
      if (array.buffer.immaterial)
        return Nop

      val dummy = if (array.inlineCounter) Const(1) else Const(0)
      (state.curChunk := (if (disjoint) bucket.dot('list) else Null)) +
          (state.curArr := (if (disjoint) state.curChunk.dot('arr) else array.buffer.name)) +
          array
            .mask
            .map(m =>
              (state.curMask := (if (disjoint) state.curChunk.dot('mask) else m.name)))
            .getOrElse(Nop) +
          (state.chunk := 0) +
          (state.count := inline(dummyCounter, base.counts.access(base.state.index))) +
          ( if (ChunkView.debug)
              Printf("Set bucket %d: spilled ? %d; count %d; inline %d",
                base.state.index, Mux(spilled, 1, 0), state.count, dummyCounter)
            else
              Nop
          ) +
          (state.numArrays :=
            Mux(state.count > 0,
              (state.count + state.chunkSize - 1) / state.chunkSize,
              1)) +
          (state.maxSlot := (Index(), maxSlotMux)) +
          (state.logVecLen := (Index(), state.maxSlot)) +
          (state.offset := (if (disjoint) Const(0) else base.offset + dummy))
    }

    def accessNumValid = None

    def access(n: Expr): LValue = {
      if (array.buffer.immaterial)
        array.buffer.name
      else
        Deref(state.curArr).sub(state.offset + n)
    }

    def absolute(n: Expr): LValue = access(n)

    def absoluteMask(n: Expr): Option[LValue] = accessMask(n)

    def accessMask(n: Expr): Option[LValue] = array.mask.map { m =>
      if (m.immaterial)
        m.name
      else
        Deref(state.curMask).sub(state.offset + n)
    }

    def append: LoAst = {
      if (array.buffer.immaterial)
        return Nop


      // Only `append` can cause an overflow of the first chunk, and thus require
      // the initialization of the separate pointer and counter arrays for this bucket.
      val spill = if (array.inlineCounter) {
        val count = base.counts.access(base.state.index)
        If(firstChunkFull && Not(spilled),
          ( if (ChunkView.debug)
              Printf("SPILL: buck %d, offset %d, dummy counter %d",
                base.state.index, state.offset, dummyCounter)
            else
              Nop
          ) +
          (state.curChunk := base.pointers.access(base.state.index).dot('list)) +
          (count := count + dummyCounter) +
          (dummyCounter := dummyCounter + 1) +
          (state.count := count) + 
          (state.spilled := True) +
          resetLocalState)
      } else {
        Nop
      }

      val inc = if (array.inlineCounter) {
        IfElse(spilled,
          (base.counts.access(base.state.index) := state.count),
          (dummyCounter := dummyCounter + 1))
      } else {
        base.counts.access(base.state.index) := state.count
      }

      spill +
      ( if (ChunkView.debug)
          If(spilled, Printf("Post spill: count %d\n", state.count))
        else 
          Nop
      ) +
      (state.curChunk := inline(Null, bucket.dot('end))) +
          (state.maxSlot := state.maxSlot + 1) +
          If(Equal(state.count % state.chunkSize, 0) && state.count > 0,
            allocChunk +
                postIncrement +
                (state.maxSlot := 1)) +
          (state.count := state.count + 1) +
          inc
    }

    override def windowLoop(body: LoAst, cursor: Option[SymLike]=None): LoAst = {
      // The chunk view needs to emit _two_ loops because this is how the chunk list 
      // traversal is hidden underneath it
      val cur = cursor.getOrElse(base.cursor.get)
      val chunk = this.cursor.get
      resetLocalState +
      ForBlock(chunk, numArrays,
        ForBlock(cur, maxCursor, body) + incrementLocalState)
    }

    def logVecLen: Expr = state.logVecLen
    def maxCursor: Expr = state.maxSlot
    def numArrays: Expr = state.numArrays
    def offset: Expr = state.offset
    def physVecLen: Expr = state.physVecLen
  }

  object ChunkView {
    var debug = false
  }

  /** Returns the [[Record]] type used to track internal metadata for hash arrays.
    *
    * @param recType The [[LoType]] of records stored in the hash array
    * @param mask If set, include a predicate mask array in the chunk struct
    * @return a [[Record]] for use in the `pointers` array
    */
  def bucketRec(recType: Data, mask: Boolean): Record = {
    val cstruct = chunkStruct(recType, mask)
    val pname = Id(recType.mangledName + "_ptrs")
    FlatRecord(
      name = Some(pname),
      fields =
          List(
            Record.Field(Ptr(cstruct), Some('list)),
            Record.Field(Ptr(cstruct), Some('end))),
      const = false)
  }

  /** Retyrns the [[Struct]] type used for a linked list of `recType` record chunks.
    *
    * Each bucket in a hash array contains a linked list of this type.
    *
    * @param recType The [[LoType]] of records used in this hash array
    * @param mask If set, include a predicate mask array in the chunk struct
    * @return a [[Struct]] for the linked list of chunks
    */
  def chunkStruct(recType: Data, mask: Boolean): Struct = {
    val lname = Id(recType.mangledName + "_list")
    val fields: List[(Id, Complete)] = if (mask) {
      List(
        'buf -> Ptr(Arr(recType)),
        'mask -> Ptr(Arr(Bool())),
        'next -> Ptr(TypeRef(lname)))
    } else {
      List(
        'buf -> Ptr(Arr(recType)),
        'next -> Ptr(TypeRef(lname)))
    }

    Struct(
      name = lname,
      fields = fields,
      false)
  }
}
