package ressort.hi
import ressort.lo
import ressort.lo.{LoType}

/** The HiRes type system.
  *
  * A `HiType` is either a scalar, a vector, an array, a hash table, a histogram, or a function:
  * 1. Scalar types ([[Scalar]]) can contain records, or `LoRes` 
  *   primitive types, which are wrapped in a [[Payload]] class.
  * 2. Vector types ([[Vec]]) denote flat extents of scalars, and can
  *   optionally be _predicated_, meaning each element is associated with
  *   an entry in a bitmask.
  * 3. Array types ([[Arr]]) are collections of either vectors or scalars,
  *   and may be nested to an arbitrary `degree`. They may also have
  *   an associated `histogram`, in a particular state:
  *     a. [[Hist.Built]]
  *     b. [[Hist.Reduced]]
  *     c. [[Hist.Restored]]
  * 4. Chunk arrays ([[Chunks]]) are like arrays but can have variable-length sub-arrays.
  *     They can be created with the [[HashTable]] and [[HashJoin]] operators and
  *     condensed with [[Compact]] into fixed-length arrays of vectors.
  */
sealed abstract class HiType {

  def hasVec: Boolean = this match {
    case Arr(t2, _, _, _, _) => t2.hasVec
    case Chunks(t2, _) => t2.hasVec
    case v: Vec => true
    case _ => false
  }

  def assertEq(other: HiType, e: Option[Object]=None) = {
    val err = {
      "TYPE MISMATCH: "+this+" where "+other+
        " expected in expression "+e+"."
    }
    assert(this == other, err)
    true
  }

  def accepts(other: HiType): Boolean


  def nonXTypeErr(typeName: String): String = {
    "Type "+this+" is not a member of type "+typeName
  }

  def nonPrimitiveTypeErr = nonXTypeErr("Primitive")
  def nonScalarTypeErr = nonXTypeErr("Scalar")
  def nonPayloadTypeErr = nonXTypeErr("Payload")
  def nonArrTypeErr = nonXTypeErr("Arr(..)")
  def nonVecTypeErr = nonXTypeErr("Vec(..)")
  def nonChunksTypeErr = nonXTypeErr("Chunks(..)")
  def nonContainerTypeErr = nonXTypeErr("Container")
  def nonBoolTypeErr = nonXTypeErr("HiResBool")

  def toScalar: Scalar = throw new AssertionError(nonScalarTypeErr)
  def toArr: Arr = throw new AssertionError(nonArrTypeErr)
  def toVec: Vec = throw new AssertionError(nonVecTypeErr)
  def toChunks: Chunks = throw new AssertionError(nonChunksTypeErr)
  def toContainer: Container = throw new AssertionError(nonContainerTypeErr)
  def toPayload: Payload = throw new AssertionError(nonPayloadTypeErr)
  def toPrimitive: Primitive = throw new AssertionError(nonPrimitiveTypeErr)
  def toHiResBool: HiResBool.type = throw new AssertionError(nonBoolTypeErr)
}


/** A [[HiType]] that is not a [[Func]] */
sealed trait Data extends HiType {
  /** The degree of nesting of an [[Arr]] or zero otherwise */
  def depth: Int = 0

  /** All layers of this [[HiType]] beneath any [[NestedData]] */
  def subArr: FlatData

  /** All layers of this [[HiType]] beneath any [[Vec]] */
  def subVec: Scalar

  /** The primitive layer of this [[HiType]] beneath any [[Mask]] */
  def subMask: Primitive

  /** Returns a version of this type with [[this.subArr]] replaced by `t` */
  def withSubArr(t: Data): Data

  /** Returns a version of this type with [[this.subVec]] replaced by `t` */
  def withSubVec(t: Scalar): Data

  /** Returns a version of this type with [[this.subMask]] replacec by `t` */
  def withSubMask(t: Primitive): Data

  /** Returns a version of this type with any [[Chunks]]s replaced by [[Arr]]s */
  def withoutChunks: Data

  /** Returns a version of this type after removing all histograms and chunk-arrays */
  def withCleanArrays: Data

  /** True iff each vector at this level has a dynamic count of initial valid records */
  def numValid: Boolean

  /** Returns a version of this type with a [[Masked]] around the innermost scalar if true */
  def withMask(masked: Boolean): Data = withSubVec(subVec.withMask(masked))

  /** Returns true iff this datatype contains a [[Masked]] */
  def masked: Boolean = subVec.masked

  /** Returns a copy of this type with `numValid` set to as indicated */
  def withNumValid(numValid: Boolean): Data = this

  /** Returns true if this type contains a [[Hist]] */
  def hasHistogram: Boolean = this match {
    case f: FlatData => false
    case a: Arr if a.histogram.nonEmpty => true
    case a: Arr => a.t.hasHistogram
    case h: Chunks => h.t.hasHistogram
  }

  /** Returns true if this type contains any [[Chunks]] */
  def hasChunks: Boolean = this match {
    case h: Chunks => true
    case a: Arr => a.t.hasChunks
    case _ => false
  }

  /** Any [[lo.Record.Field]]s in this type when used as the implicit record */
  def fields: Seq[lo.Record.Field] = subMask match {
    case p: PayloadLike => p.loType match {
      case r: lo.Record => r.fields
      case n: lo.NonRec => p match {
        case n: NamedPayload =>
          Seq(lo.Record.Field(lo.LoType(p).toNonRec, name=Some(lo.Id(n.name.name))))
        case other => Seq(lo.Record.Field(lo.LoType(other).toNonRec))
      }
      case lo.NoType => ???
    }
    case p: Primitive => Seq(lo.Record.Field(lo.LoType(p).toNonRec))
  }
}

/** Represents the output of a histogram operator.
  *
  * Some array operators produce or consume _histograms_,
  * which track the lengths of variable-sized sub-arrays (elements of [[Arr]]s).
  * They may or may not have semantic value, such as a range of
  * bits used as a radix or list of range delimiters.
  *
  * The `HiType` type system encodes the presence of such histograms, as well as
  * their _state_, in order to ensure that operations are applied in
  * the prescribed order.
  * Histograms are also _affine_ types, in that histograms in most states can
  * be used _only once_, since they are modified in-place;
  * any attempt to use a histogram in the `Initialized` state
  * with multiple operators will result in a type error.
  */
case class Hist(state: Hist.State) extends FlatData {
  // If any of these methods are called, it's a sign that something has gone
  // wrong, as only histogram-specific operators should operate on histogram types
  def vec: Vec = ???
  def flattenVec = ???

  def withSubVec(t2: Scalar) = this
  def numValid = false
  def subArr: FlatData = this

  def subMask: Primitive = subVec
  def subVec = Payload(lo.Index())
  def withSubArr(t: Data): ressort.hi.Data = t

  def withSubMask(t: Primitive): ressort.hi.FlatData = t
  override def withMask(masked: Boolean) = this
  override def masked = false
  def accepts(other: HiType): Boolean = other match {
    case Hist(state) => (state == this.state)
    case _ => false
  }
}

object Hist {
  sealed trait State
  case object Built extends State
  case object Reduced extends State
  case object Moved extends State
}

sealed abstract class Scalar extends FlatData {
  def subArr: Scalar = this

  def vecToHtbl: Scalar  = this
  def withSubArr(t: Data): Data = t

  def withSubMask(t: Primitive): Scalar = t

  override def toScalar: this.type = this

  override def subVec: this.type = this

  override def withMask(masked: Boolean): Scalar = this match {
    case Masked(p) if masked => Masked(p)
    case Masked(p) => p
    case p: Primitive if masked => Masked(p)
    case _ => this
  }

  override def withNumValid(numValid: Boolean): this.type = this

  def numValid = false
  override def masked = this match { case m: Masked => true; case _ => false }
  def padded = false

  def vec: Vec = ???

  def withSubVec(t2: Scalar): Scalar = t2
}


abstract class Primitive extends Scalar {
  override def toPrimitive: Primitive = this
}

case class Masked(p: Primitive) extends Scalar {
  override def withSubMask(t: Primitive): Masked = copy(t)

  def subMask: Primitive = p

  def accepts(other: HiType): Boolean = other match {
    case Masked(p2) => p.accepts(p2)
    case _ => false
  }
}

sealed trait PayloadLike extends Primitive {
  def loType: lo.Primitive
  def subMask: PayloadLike = this
  override def toString = loType.toString

  def accepts(other: HiType): Boolean = (loType, other) match {
    case (i: lo.IntValued, HiResInt) => true
    case (_, pl: PayloadLike) => loType.accepts(pl.loType)
    case _ => false
  }
}

case class Payload(loType: lo.Primitive) extends PayloadLike
case class NamedPayload(name: Id, nonRec: lo.NonRec) extends PayloadLike {
  def loType = nonRec
}


object HiResBool {
  def apply: Primitive = Payload(lo.Bool())
}

case object HiResInt extends Primitive {
  def subMask: Primitive = this
  def accepts(other: HiType): Boolean = other match {
    case Payload(i: lo.IntValued) => true
    case HiResInt => true
    case _ => false
  }
}

case object HiUnit extends HiType {
  def accepts(other: HiType) = false
}


sealed trait Container extends Data {
  def withSubVec(s: Scalar): Container

  override def withMask(masked: Boolean): Container = this
}

/** A [[HiType]] that is not an [[Arr]] */
sealed trait FlatData extends Data {
  def withSubVec(s: Scalar): FlatData

  def withSubMask(t: Primitive): FlatData

  def withoutChunks: FlatData = this

  def withCleanArrays: FlatData = this
}

/** A [[Container]] that is nested: not just a vector or scalar */
sealed trait NestedData extends Container {
  def base: Data

  def withBase(base: Data): NestedData

  def withSubVec(s: Scalar): NestedData

  def withSubMask(t: Primitive): NestedData

  override def withSubArr(t: Data): NestedData

  def withoutChunks: NestedData

  def withCleanArrays: NestedData

  /** Flattens the innermost layer of nesting of this type */
  def flatten: Data = {
    val nonNestedArrErr = "Can't flatten a non-nested array in type "+this
    val numValidDropErr = "Can't drop a num-valid counter from an array in type "+this
    val paddingDropErr  = "Can't drop padding from an array without compaction in type "+this
    val disjointDropErr  = "Can't drop disjointedness from an array without compaction in type "+this
    val chunkDropErr = "Can't drop chunkiness without compaction in type "+this

    base match {
      case n: NestedData => withBase(n.flatten)
      case s: Scalar => throw new AssertionError(nonNestedArrErr)
      case _ => this match {
        case a: Arr if (a.disjoint) => throw new AssertionError(disjointDropErr)
        case a: Arr if (a.numValid) => throw new AssertionError(numValidDropErr)
        case a: Arr if (a.padded) => throw new AssertionError(paddingDropErr)
        case c: Chunks => throw new AssertionError(chunkDropErr)
        case _ => base
      }
    }
  }

  /** The innermost nested level of this type */
  def innermost: NestedData = base match {
    case n: NestedData => n.innermost
    case _ => this
  }

  def withInnermost(t: NestedData): NestedData = base match {
    case n: NestedData => withBase(n.withInnermost(t))
    case _ => t
  }

}

case class Arr(
    t: Data,
    histogram: Option[Data]=None,
    numValid: Boolean=false,
    padded: Boolean=false,
    disjoint: Boolean=false)
  extends NestedData {

  def withBase(base: Data): Arr = copy(t = base)
  def base: Data = t

  def subArr: FlatData = t.subArr

  def subMask: Primitive = t.subMask
  def withSubArr(t: Data): Arr = copy(this.t.withSubArr(t))

  def withSubMask(t: Primitive): Arr = copy(t = this.t.withSubMask(t))

  override def toArr: Arr = this

  override def depth: Int = t match {
    case a: Arr => 1 + a.depth
    case _ => 1
  }

  def accepts(other: HiType): Boolean = {
    (this, other) match {
      case (Arr(t1, Some(h1), n1, p1, d1), Arr(t2, Some(h2), n2, p2, d2)) => {
        t1.accepts(t2) && h1.accepts(h2) && n1 == n2 && p1 == p2 && d1 == d2
      }
      case (Arr(t1, None, n1, p1, d1), Arr(t2, None, n2, p2, d2)) => {
        t1.accepts(t2) && n1 == n2 && p1 == p2 && d1 == d2
      }
      case _ => false
    }
  }

  def subVec: Scalar = t.subVec

  override def withSubVec(s: Scalar): Arr = {
    this.copy(t = this.t.withSubVec(s))
  }

  override def withMask(masked: Boolean): Arr = this.copy(t = t.withMask(masked))

  override def withNumValid(numValid: Boolean): Arr = this.copy(numValid = numValid)

  def withoutChunks = copy(t.withoutChunks)

  def withCleanArrays = copy(t.withCleanArrays, histogram = None)

  override def hasChunks = t.hasChunks

}

case class Chunks(t: Data, disjoint: Boolean=false) extends NestedData {
  override def depth: Int = 1 + t.depth

  def base: Data = t
  def withBase(base: Data): Chunks = copy(t = base)

  def subArr = t.subArr

  def subMask: Primitive = t.subMask
  def withSubArr(t: Data): Chunks = copy(t = this.t.withSubArr(t))

  def withSubMask(t: Primitive): Chunks = copy(t = this.t.withSubMask(t))

  override def toChunks: Chunks = this

  def withSubVec(s: Scalar): Chunks = copy(t.withSubVec(s))

  def numValid: Boolean = true

  def subVec = t.subVec

  def withoutChunks = Arr(t)

  def withCleanArrays = Arr(t.withCleanArrays)

  def accepts(other: HiType): Boolean = other match {
    case c: Chunks => t.accepts(c.t)
    case _ => false
  }
}

case class Vec(s: Scalar, numValid: Boolean=false) extends Container with FlatData  {
  def subVec: Scalar = s

  def subArr: Vec = this

  def subMask: Primitive = s.subMask
  def withSubArr(t: Data): Data = t

  def withSubMask(t: Primitive): Vec = copy(s = this.s.withSubMask(t))
  def withSubVec(s: Scalar): Vec = copy(s = s)

  def accepts(other: HiType): Boolean = other match {
    case Vec(s2, nv2) => s.accepts(s2) && numValid == nv2
    case _ => false
  }

  override def toContainer: Vec = this

  def vec = this

  override def withMask(masked: Boolean): Vec = {
    this.copy(s.withMask(masked))
  }

  override def withNumValid(numValid: Boolean): Vec = this.copy(numValid = numValid)
}

case class MultiHiType(head: Data, tail: Data*) extends Data {
  def flattenVec = ???
  def subVec = ???
  def withSubVec(s          : Scalar) = ???
  def vec = ???


  def subArr: FlatData = ???

  def subMask: Primitive = head.subMask
  def withSubArr(t: Data): Data = ???
  def withoutChunks = ???
  def withCleanArrays = ???

  def withSubMask(t: Primitive): Data = ???

  override def hasChunks = ???
  override def withMask(masked: Boolean) = ???
  override def masked = ???
  def numValid = false
  def accepts(other: HiType): Boolean = other match {
    case mh: MultiHiType => tail.zip(mh.tail).foldLeft(head.accepts(mh.head)) {
      case (b, (d1, d2)) => b && d1.accepts(d2)
    }
    case _ => false
  }
}


case class Func(from: Map[Id, Data], to: Data) extends HiType {
  to match {
    case f: Func => ???
    case _ =>
  }
  def accepts(other: HiType) = false
}
