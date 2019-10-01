// See LICENSE.txt
package ressort.lo.interp
import scala.collection.mutable.HashSet
import ressort.lo._

/** Represents a unique address in the interpreter's simulated memory system.
  *
  * Whenever an LoRes object is allocated in the interpreter, a corresponding
  * `EAddr` is allocated in the JVM.  The `EAddr`'s address represents the
  * address of the LoRes object; thus, taking a reference to an LoRes object
  * yields its companion `EAddr`.
  */
class EAddr(var value: EVal=ENoVal)

object ENull extends EAddr(ENoVal)

/** Holds a concrete value created during interpreter execution. */
sealed abstract class EVal {
  def err(typeName: String, lines: Option[LoAstLines]) = {
    throw InterpError(s"$this used where $typeName required.", lines, uninitialized=(this==ENoVal))
  }
  def toEInt(lines: Option[LoAstLines]): EInt = { err("EInt", lines) }
  def toEFloat(lines: Option[LoAstLines]): EFloat = { err("EFloat", lines) }
  def toEDouble(lines: Option[LoAstLines]): EDouble = { err("EDouble", lines) }
  def toEBits(lines: Option[LoAstLines]): EBits = { err("EBits", lines) }
  def toEBool(lines: Option[LoAstLines]): EBool = { err("EBool", lines) }
  def toEPtr(lines: Option[LoAstLines]): EPtr = { err("EPtr", lines) }
  def toEArray(lines: Option[LoAstLines]): EArray = { err("EArray", lines) }
  def toEFunc(lines: Option[LoAstLines]): EFunc = { err("EFunc", lines) }
  def toERecord(lines: Option[LoAstLines]): ERecord = { err("ERecord", lines) }
  def toEStruct(lines: Option[LoAstLines]): EStruct = { err("EStruct", lines) }
  def toENumber(lines: Option[LoAstLines]): ENumber = { err("ENumber", lines) }
  def compare(that: EVal, lines: Option[LoAstLines]): Int = { err("(comparable value)", lines) }

  def dumpLines(
      childLines: Seq[String]=Seq(), 
      markedSet: HashSet[EAddr]=HashSet())
      (implicit venv: Option[LoInterp]): Seq[String] = {
    childLines.map { line => "    "+line } ++ Seq(this.toString+"\n")
  }
}

/** Equivalent to NULL.
  *
  * Whenever a new LValue is created, it initially contains `ENoVal`.  This
  * allows detecting the use of uninitialized values.
  */
case object ENoVal extends EVal

/** Holds any scalar value, which must be convertible to a [[scala.math.BigInt]]
  * raw bits representation.
  */
sealed abstract class EScalar extends EVal {
  def toBits: BigInt
}

object EInt {
  def apply(n: Long, loType: IntValued): EInt = {
    loType match {
      case i: LoInt => EInt(n, 4, true)
      case i: UInt => EInt(n, 4, false)
      case i: Index => EInt(n, 4, false)

      case i: UInt8 => EInt(n, 1, false)
      case i: UInt16 => EInt(n, 2, false)
      case i: UInt32 => EInt(n, 4, false)
      case i: UInt64 => EInt(n, 8, false)

      case i: LoInt8 => EInt(n, 1, true)
      case i: LoInt16 => EInt(n, 2, true)
      case i: LoInt32 => EInt(n, 4, true)
      case i: LoInt64 => EInt(n, 8, true)
    }
  }
}

/** Represents a concrete numeric value that can be an integer or floating point */
sealed trait ENumber extends EVal {
  def log2Up: EInt
  def toInt: Int
  def isNegative: Boolean
  def isZero: Boolean

  def compare(other: ENumber): Int

  override def toENumber(lines: Option[LoAstLines]): ENumber = this
}

sealed trait ENumberLike[T <: ENumberLike[T]] extends Ordered[T] { this: ENumber =>
  def pow2: T
  def pow(o: T): T

  def +(o: T): T
  def -(o: T): T
  def *(o: T): T
  def /(o: T): T
  def unary_- : T
}



case class EFloat(f: Float) extends ENumber with ENumberLike[EFloat] {
  def toInt: Int = f.toInt
  def isNegative = (f < 0.0f)
  def isZero = (f == 0.0f)

  override def toEFloat(lines: Option[LoAstLines]): EFloat = this
  override def toEDouble(lines: Option[LoAstLines]): EDouble = EDouble(f.toDouble)
  override def toEInt(lines: Option[LoAstLines]): EInt = EInt(f.toInt, widthBytes = 4)

  def +(o: EFloat) = EFloat(f + o.f)
  def -(o: EFloat) = EFloat(f - o.f)
  def *(o: EFloat) = EFloat(f * o.f)
  def /(o: EFloat) = EFloat(f / o.f)

  def unary_- : EFloat = EFloat(-f)

  def pow2: EFloat = EFloat(math.pow(2.0, f).toFloat)
  def pow(o: EFloat) = EFloat(math.pow(f, o.f).toFloat)
  def log2Up: EInt = EInt((math.log(f)/math.log(2.0)).toInt, widthBytes = 4)

  def compare(other: EFloat): Int = f.compare(other.f)

  def compare(other: ENumber): Int = other match {
    case EFloat(f2) => f.compare(f2)
    case EDouble(d2) => f.toDouble.compare(d2)
    case i: EInt => f.compare(i.toEFloat(None).f)
  }
}

case class EDouble(d: Double) extends ENumber with ENumberLike[EDouble] {
  def toInt: Int = d.toInt
  def isNegative = (d < 0.0d)
  def isZero = (d == 0.0d)

  override def toEFloat(lines: Option[LoAstLines]): EFloat = EFloat(d.toFloat)
  override def toEDouble(lines: Option[LoAstLines]): EDouble = this
  override def toEInt(lines: Option[LoAstLines]): EInt = EInt(d.toLong, widthBytes = 8)

  def +(o: EDouble) = EDouble(d + o.d)
  def -(o: EDouble) = EDouble(d - o.d)
  def *(o: EDouble) = EDouble(d * o.d)
  def /(o: EDouble) = EDouble(d / o.d)

  def unary_- : EDouble = EDouble(-d)

  def pow2: EDouble = EDouble(math.pow(2.0, d))
  def pow(o: EDouble) = EDouble(math.pow(d, o.d))
  def log2Up: EInt = EInt((math.log(d)/math.log(2.0)).toInt, widthBytes = 4)

  def compare(other: EDouble): Int = d.compare(other.d)

  def compare(other: ENumber): Int = other match {
    case EFloat(f2) => d.compare(f2.toDouble)
    case EDouble(d2) => d.compare(d2)
    case i: EInt => d.compare(i.toEDouble(None).d)
  }
}

/** Represents any of the LoRes integer types.
  *
  * @param i Actual bits of data representing this value.
  */
case class EInt(
      i: Long, 
      widthBytes: Int=4, 
      signed: Boolean=true)
    extends ENumber with ENumberLike[EInt] {

  assert(widthBytes <= 8, s"EInt[_] larger than a double-word not supported.")


  /** Returns a [[BigInt]] version of this value, appropriately
    * sign-extending if this is a signed type.
    */
  def toBigInt: BigInt = {
    val BytesPerLong = 8
    val signBit = 1L << ((widthBytes * 8) - 1)
    val sign = i & signBit
    val signMask = ~((signBit - 1L) | signBit)
    val res = if (sign != 0 && signed)
      BigInt(i | signMask)
    else
      BigInt(i & ~signMask)
    res
  }

  def isNegative = (i < 0L)
  def isZero = (i == 0L)
  def toInt = i.toInt

  def toBits = toBigInt

  override def toEInt(lines: Option[LoAstLines]): EInt = this
  override def toEFloat(lines: Option[LoAstLines]): EFloat = EFloat(toBigInt.toFloat)
  override def toEDouble(lines: Option[LoAstLines]): EDouble = EDouble(toBigInt.toDouble)


  def fromBigInt(bi: BigInt): EInt = {
    val mask = if (widthBytes == 8) (-1L) else (1L << (widthBytes * 8)) - 1
    EInt(bi.toLong & mask, widthBytes=widthBytes, signed=signed)
  }

  def lowerEInt: EInt = EInt(0).fromBigInt(toBigInt)

  /** Returns an `EInt` whose `widthBytes` and `signed` parameters 
    * correspond to the result of a binary operation applied to `this`
    * and `o`.  Resulting `i` value is undefined.
    */
  def rt(o: EInt): EInt = {
    def max[T <% Ordered[T]](a: T, b: T): T = if (a > b) a else b
    val resSigned = signed || o.signed
    val resWidth = max(widthBytes, o.widthBytes)
    EInt(-7777, widthBytes=resWidth, signed=resSigned)
  }


  def +(o: EInt): EInt = rt(o).fromBigInt(toBigInt + o.toBigInt)
  def -(o: EInt): EInt = rt(o).fromBigInt(toBigInt - o.toBigInt)
  def *(o: EInt): EInt = rt(o).fromBigInt(toBigInt * o.toBigInt)
  def /(o: EInt): EInt = rt(o).fromBigInt(toBigInt / o.toBigInt)
  def %(o: EInt): EInt = rt(o).fromBigInt(toBigInt % o.toBigInt)
  def unary_- :   EInt = fromBigInt(-toBigInt)
  def <<(o: EInt): EInt = rt(o).fromBigInt(toBigInt << o.lowerEInt.i.toInt)
  def >>(o: EInt): EInt = {
    val shamt = o.lowerEInt.i.toInt
    var res = toBigInt >> shamt
    if (!signed) {
      val mask = (BigInt(1) << (64 - shamt)) - 1
      res = res & mask
    }
    rt(o).fromBigInt(res)
  }


  def pow2: EInt = fromBigInt(BigInt(1) << lowerEInt.i.toInt)
  def pow(o: EInt): EInt = rt(o).fromBigInt(toBigInt.pow(o.toBigInt.toInt))
  def log2Up: EInt = fromBigInt(toBigInt.bitLength)

  def range(lsb: EInt, msb: EInt): EInt = {
    val lsbBI = lsb.toBigInt
    val msbBI = msb.toBigInt
    
    val negRange = "Bit ranges must be non-negative!"
    assert(lsbBI >= BigInt(0), s"LSB $lsbBI: $negRange")
    assert(msbBI >= BigInt(0), s"MSB $msbBI: $negRange")
    
    val bigRange = "Bit ranges must be <= 64"
    assert(lsbBI <= BigInt(64), s"LSB $lsbBI: $bigRange")
    assert(msbBI <= BigInt(64), s"MSB $msbBI: $bigRange")
    range(msbBI.intValue, lsbBI.intValue)
  }

  def range(lsb: Int, msb: Int): EInt = {
    val widthBits = msb - lsb + 1
    val widthBytes = (widthBits + 7) / 8
    val mask = (BigInt(1) << widthBits) - 1
    val sla = (toBigInt >> lsb) & mask
    val res = EInt(0, widthBytes=widthBytes, signed=false).fromBigInt(sla)
    res
  }

  def &(o: EInt): EInt = EInt(0, widthBytes=widthBytes, signed=signed).fromBigInt(toBigInt & o.toBigInt)

  def compare(o: EInt): Int = {
    val bigRes = toBigInt - o.toBigInt
    val res = if (bigRes < BigInt(0))
      -1
    else if (bigRes == BigInt(0))
      0
    else
      1
    res
  }

  override def compare(o: EVal, lines: Option[LoAstLines]): Int = compare(o.toEInt(lines))

  def compare(other: ENumber): Int = other match {
    case d: EDouble => toEDouble(None).compare(other)
    case f: EFloat => toEFloat(None).compare(other)
    case i: EInt => compare(i)
  }

  def equiv(o: EInt, lines: Option[LoAstLines]): Boolean = (compare(o, lines) == 0)
}


case class EBits(bits: BigInt) extends EVal { 
  override def toEBits(lines: Option[LoAstLines]) = this
  override def compare(that: EVal, lines: Option[LoAstLines]): Int = {
    val bigRes = bits - that.toEBits(lines).bits
    if(bigRes < BigInt(0))
      -1
    else if(bigRes == BigInt(0))
      0
    else
      1
  }
}
case class EBool(b: Boolean) extends EVal { 
  override def toEBool(lines: Option[LoAstLines]) = this
}

case class EPtr(ref: EAddr) extends EVal {
  override def toEPtr(lines: Option[LoAstLines]) = this
  override def dumpLines(
      childLines: Seq[String], 
      markedSet: HashSet[EAddr])
      (implicit venv: Option[LoInterp]): Seq[String] ={
    val targetLines = venv match {
      case Some(venv2) => {
        if(markedSet.contains(ref)) {
          Seq()
        } else {
          ref.value.dumpLines(markedSet=markedSet) map { l => "    "+l }
        }
      }
      case None => Seq()
    }
    Seq("Pointer to "+ref+":\n") ++ targetLines
  }
}

case class ERecord(fields: IndexedSeq[EAddr]) extends EVal {
  override def toERecord(lines: Option[LoAstLines]): ERecord = this
}

case class EArray(
    a: Array[EAddr], 
    len: Int) extends EVal {
  override def toEArray(lines: Option[LoAstLines]) = this

  override def toString() = {
    val items = (a map { item => item.toString }).toList match {
      case h::Nil => h
      case h::t => t.foldLeft(h){ (h,t) => h+", "+t }
      case Nil => ""
    }
    "Array: [ " + items + " ]"
  }

  override def dumpLines(
      childLines: Seq[String]=Seq(),
      markedSet: HashSet[EAddr]=HashSet())
      (implicit venv: Option[LoInterp]=None): Seq[String] = {
    val myLines = a.take(20).foldLeft(Seq[String]()) {
      case (lines, item) => lines ++ {
        val lines = item.value.dumpLines(markedSet=markedSet+item)
        lines map { line => "    " + line  }
      }
    }
    val allLines: Seq[String] = (childLines map { line => "    "+line }) ++ myLines
    Seq("Array: ["+len+"]\n") ++ allLines
  }
}

case class EFunc(
    params: Seq[(Id, LoType)],
    body: TypedLoAst)
  extends EVal { 
  
  override def toEFunc(lines: Option[LoAstLines]) = this
}

case class EStruct(
    fields: Seq[(Id, EAddr)])
  extends EVal {
  
  override def toEStruct(lines: Option[LoAstLines]) = this

  override def dumpLines(
      childLines: Seq[String]=Seq(),
      markedSet: HashSet[EAddr]=HashSet())
      (implicit venv: Option[LoInterp]=None): Seq[String] = {
    var myLines = List[String]()
    myLines = s"Struct : {\n" :: myLines
    var mset = markedSet
    for ((name, addr) <- fields) {
      myLines = s"\t$name -> $addr :\n" :: myLines
      mset += addr
      val itemLines = addr.value.dumpLines(markedSet=mset)
      for (l <- itemLines)
        myLines = l :: myLines
    }
    myLines = "}\n" :: myLines
    myLines.reverse
  }
}
