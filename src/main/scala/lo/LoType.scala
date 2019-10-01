// See LICENSE.txt
package ressort.lo
import ressort.hi
import ressort.util

import scala.collection.mutable.HashMap

/** Defines the LoRes type system. */
sealed abstract class LoType {
  val const: Boolean

  def isContainer() = false 
  def nonContainerErr() = this+" is not a container type"
  def nonFuncErr() = this+" is not a function"
  def nonPtrErr() = this+" is not a pointer"
  def nonRecordErr() = this+" is not a Record type"
  def nonPrimitiveErr() = this+" is not a Primitive type"
  def nonNonRecErr() = this+" is not a NonRec type"
  def nonAllocatableErr() = this+" is not an allocatable type"
  def prefixSumTypeErr() = this+" is not an arry of ints"
  def nonIntValuedErr() = this+" is not an integer-valued type"
  def nonFixedWidthIntErr() = this+" is not an fixed-width integer type"
  def nonStructErr() = this+" is not a Struct type"
  def nonDataErr() = this+" is not a Data type"
  def nonScalarErr() = this+" is not a Scalar type"
  def nonCompleteErr() = this+" is not a Complete type"
  def mismatchErr(t2: LoType) = {
    val err = "TYPE MISMATCH: "+this+" not convertible to "+t2
    err
  }
  
  def toRecord: Record = throw new AssertionError(nonRecordErr())
  def toArr: Arr = throw new AssertionError(nonContainerErr())
  def toFunc: Func = throw new AssertionError(nonFuncErr())
  def toPtr: Ptr = throw new AssertionError(nonPtrErr())
  def toStruct: Struct = throw new AssertionError(nonStructErr())
  def toData: Data = throw new AssertionError(nonDataErr())
  def toPrimitive: Primitive = throw new AssertionError(nonPrimitiveErr())
  def toNonRec: NonRec = throw new AssertionError(nonNonRecErr())
  def toComplete: Complete = throw new AssertionError(nonCompleteErr())
  def toScalar: Scalar = throw new AssertionError(nonScalarErr())
  def toIntValued: IntValued = throw new AssertionError(nonIntValuedErr())
  def toFixedWidthInt: FixedWidthInt = throw new AssertionError(nonFixedWidthIntErr())
  def isComparable: Boolean = false


  /** Implementations of [[mangledName]] can use this to emit the string 
    * "const_" as a prefix to their `mangledName`s where necessary.
    */
  def constPrefix: String = if (const) "const_" else ""

  /** The name for this type that could be used in generated C++ code. */
  def mangledName: String 
 
  /** Each child type must provide a way to get a copy of an instance
    * with the value of [[const]] set to `c`.
    */
  def setConst(c: Boolean): LoType

  final def nonConst: LoType = setConst(false)

  /** Returns true iff a value of type `t2` be assigned to an `LValue`
    * of this type.
    *
    * Some subclasses will want to override this definition. For instance,
    * [[IntValued]] will allow any cast to a wider type or sign conversion.
    */
  def accepts(t2: LoType): Boolean = this == t2.nonConst

  /** Returns a resulting [[LoType]] iff a value of type `t2` can be combined 
    * with a value of this type in a binary expression.
    * 
    * Types should override the default definition when they support implicit
    * conversions.  For example, adding a [[UInt8]] to an [[LoInt]] will result
    * in an `LoInt`.
    */
  def combine(t2: LoType): Option[LoType] = {
    if (accepts(t2))
      Some(this)
    else
      None
  }
}

object LoType {
  /** Returns the `LoRes` equivalent of the given `hiType` */
  def apply(hiType: hi.HiType): LoType = {
    hiType match {
      case hi.HiResInt => Index()
      case hi.HiUnit => NoType
      case hi.Arr(t2, _, _, _, _) => Arr(LoType(t2).toData)
      case hi.Vec(t2, _) => Arr(LoType(t2).toData)
      case hi.Func(_, _) => throw new AssertionError(Err.illegalFuncType(hiType))
      case hi.Payload(loType) => loType
      case hi.NamedPayload(_, loType) => loType
      case hi.Masked(t2) => LoType(t2)
      case other => throw new AssertionError(Err.illegalTypeTrans(other))
    }
  }
}

/** Includes all [[ressort.lo.LoType]]s that contain data */
sealed trait Data extends LoType {
  override def toData: Data = this

  /** Either this type if it is scalar, or its elements' type if it is an array. */
  def scalarType: Scalar
}

/** Includes all [[ressort.lo.LoType]]s that are not arrays */
sealed trait Scalar extends Data {
  override def toScalar: Scalar = this
  def scalarType = this
  def setConst(c: Boolean): Scalar
}

/** A kind of [[ressort.lo.LoType]] that is complete enough to be allocated */
sealed trait Complete extends Scalar {
  override def toComplete: Complete = this
}

/** This is either a record type or could be a field of one. */
sealed trait Primitive extends Complete {
  override def toPrimitive: Primitive = this
}

/** This type contains no distinct sub-fields */
sealed trait NonRec extends Primitive {
  override def toNonRec: NonRec = this
  def setConst(c: Boolean): NonRec

  def widthBytes: Int
}


case object NoType extends Primitive {
  val const = true

  /** Since an object of type `NoType` cannot be assigned to
    * it is not allowed to have `const == false`.
    */
  def setConst(c: Boolean) = this

  override def mangledName = "NoType"
}

/** Represents any (signed or unsigned) integer datatype.
  *
  * @param minBytes The minimum number of bytes this type is guaranteed to
  *                 have on any target platform
  *
  * @param maxBytes The maximum number of bytes this type is guaranteed not
  *                 to excede on any target platform
  *
  * @param signed   True iff this type is signed.
  */
sealed abstract class IntValued(
    val minBytes: Int,
    val maxBytes: Int,
    val signed: Boolean=true)
  extends NonRec {
  
  override def toIntValued: IntValued = this
  
  override def isComparable = true

  override def accepts(t2: LoType): Boolean = t2 match {
    case iv: IntValued => !const
    case _ => false
  }

  override def combine(t2: LoType): Option[LoType] =  t2 match {
    case iv: IntValued if (this.maxBytes >= iv.maxBytes) => Some(this)
    case iv: IntValued => Some(iv)
    case other => None
  }

  lazy val className = getClass.getName.drop("ressort.lo.".length)

  override def mangledName = constPrefix + className

  def widthBytes = maxBytes
}

sealed abstract class FixedWidthInt(val bytes: Int, signed: Boolean=true) 
  extends IntValued(bytes, bytes, signed) 
{
  override def toFixedWidthInt = this
}

case class LoInt(const: Boolean=false) extends IntValued(4, 8) {
  def setConst(c: Boolean) = copy(const=c)
}
case class UInt(const: Boolean=false) extends IntValued(4, 8, false) {
  def setConst(c: Boolean) = copy(const=c)
}
case class Index(const: Boolean=false) extends IntValued(4, 8, false) {
  def setConst(c: Boolean) = copy(const=c)
}

case class UInt8(const: Boolean=false) extends FixedWidthInt(1, false) {
  def setConst(c: Boolean) = copy(const=c)
}
case class UInt16(const: Boolean=false) extends FixedWidthInt(2, false) {
  def setConst(c: Boolean) = copy(const=c)
}
case class UInt32(const: Boolean=false) extends FixedWidthInt(4, false) {
  def setConst(c: Boolean) = copy(const=c)
}
case class UInt64(const: Boolean=false) extends FixedWidthInt(8, false) {
  def setConst(c: Boolean) = copy(const=c)
}

case class LoInt8(const: Boolean=false) extends FixedWidthInt(1) {
  def setConst(c: Boolean) = copy(const=c)
}
case class LoInt16(const: Boolean=false) extends FixedWidthInt(2) {
  def setConst(c: Boolean) = copy(const=c)
}
case class LoInt32(const: Boolean=false) extends FixedWidthInt(4) {
  def setConst(c: Boolean) = copy(const=c)
}
case class LoInt64(const: Boolean=false) extends FixedWidthInt(8) {
  def setConst(c: Boolean) = copy(const=c)
}

case class LoFloat(const: Boolean=false) extends NonRec {
  def mangledName = "float"

  def setConst(c: Boolean) = copy(const=c)

  override def accepts(t2: LoType): Boolean = t2 match {
    case LoFloat(_) => true
    case i: IntValued => true
    case _ => false
  }

  def widthBytes = 4
}

case class LoDouble(const: Boolean=false) extends NonRec {
  def mangledName = "double"

  def setConst(c: Boolean) = copy(const=c)

  override def accepts(t2: LoType): Boolean = t2 match {
    case LoFloat(_) => true
    case LoDouble(_) => true
    case iv: IntValued => (true)
    case _ => false
  }

  def widthBytes = 8
}

case class Bits(const: Boolean=false) extends LoType {
  def setConst(c: Boolean) = copy(const=c)
  def mangledName = {
    throw new AssertionError("Bits type does not have mangled name")
  }
}

case class Arr(
    elementType: Data, 
    const: Boolean=false) extends Data { 
  assert(scalarType != NoType) 
  override def toArr = this

  def scalarType = elementType.scalarType

  def setConst(c: Boolean) = copy(const=c)

  override def mangledName = constPrefix+"array__"+scalarType.mangledName
}

case class Ptr(loType: LoType, const: Boolean=false) extends NonRec {
  override def toPtr: Ptr = this
  
  /** Allows constant pointers to mutable objects. */
  override def accepts(t2: LoType): Boolean = (this, t2) match {
    case (_, NullType) => true
    case (Ptr(Arr(lt1, _), _), Ptr(Arr(lt2, _), _)) if (!const) =>{
      Ptr(lt1).accepts(Ptr(lt2))
    }
    case (Ptr(lt1, _), Ptr(lt2, _)) if (!const) => lt1.nonConst.accepts(lt2)
    case _ => super.accepts(t2)
  }

  def setConst(c: Boolean) = copy(const=c)

  override def mangledName = constPrefix + "ptr_" + loType.mangledName

  def widthBytes = 8
}

case object NullType extends NonRec {
  val const = false
  val mangledName = "NullType"
  def setConst(c: Boolean) = this
  def widthBytes = Index().widthBytes

  override def accepts(t2: LoType): Boolean = t2 match {
    case p: Ptr => true
    case NullType => true
    case _ => false
  }
}

case class Bool(const: Boolean=false) extends NonRec {
  def setConst(c: Boolean) = copy(const=c)

  override def mangledName = "bool"

  def widthBytes = 1
}

case class Func(
    params: Seq[(Id, LoType)],
    retType: Option[Primitive]=None) extends LoType {
  override def toFunc: Func = this
  val const = true
  def setConst(c: Boolean) = this
  def mangledName = {
    throw new AssertionError("functions do not have mangled names")
  }
}

case class Struct(
    name: Id, 
    fields: Seq[(Id, Complete)],
    const: Boolean=false) extends Complete {
  override def toStruct: Struct = this
  override def toString: String = name.toString
  def fullName: String = {
    s"struct $name {\n"+
    util.reduceNewline(
      fields map { case (id, loType) => s"\t$id:\t${loType.mangledName}" }) +
    "}"
  }
  def setConst(c: Boolean) = copy(const=c)

  override def mangledName = constPrefix + "struct_" + name

  override def accepts(t2: LoType): Boolean = t2 match {
    case TypeRef(name, _) if (!const) => name == this.name
    case Struct(name, fields, _) if (!const) => {
      (name == this.name)
    }
    case _ => false
  }

  lazy val fieldMap: Map[String, Complete] = {
    Map(fields.map(f => f._1.name -> f._2):_*)
  }
}

case class TypeRef(name: Id, const: Boolean=false) extends Scalar { 
  def setConst(c: Boolean): TypeRef = copy(const = c)

  def mangledName = constPrefix + name.name

  override def accepts(t2: LoType): Boolean = {
    t2 match {
      case TypeRef(name, _) if (!const) => name == this.name
      case Struct(name, fields, _) if (!const) => name == this.name
      case _ => false
    }
  }
}

/** Represents data with named or anonymous fields, in row- of column-major order
  *
  * To actually refer to a column of data, a [[Record]] should be wrapped in a [[Vec]]
  * and some number (possibly zero) of [[Arr]] layers.
  */
sealed trait Record extends Primitive {
  def fields: Seq[Record.Field]

  def name: Option[Id]

  lazy val namedFields: Map[String, Record.Field] = {
    fields.filter(_.name.nonEmpty).map(f => f.name.get.name -> f).toMap
  }

  def apply(id: Id): Record.Field = namedFields(id.name)

  def apply(n: Int): Record.Field = fields(n)

  override def toRecord: this.type = this

  override def accepts(t2: LoType): Boolean = {
    if (const || !t2.isInstanceOf[Record])
      return false

    val t2rec = t2.toRecord

    if ((name.nonEmpty && t2rec.name.nonEmpty && name != t2rec.name) ||
        (fields.length != t2rec.fields.length)) {
      return false
    }

    for ((f1, f2) <- fields.zip(t2rec.fields)) {
      if (!f1.loType.accepts(f2.loType) ||
          (f1.name.nonEmpty && f1.name != f2.name))
        return false
    }

    true
  }
}

/** A record in which fields are stored contiguously.
  *
  * This corresponds to a single-column (row-major) relation.
  */
case class FlatRecord(
    fields: Seq[Record.Field],
    name: Option[Id],
    const: Boolean=false)
  extends Record {

  def setConst(c: Boolean) = copy(const = c)

  def mangledName: String = {
    name.map(id => return id.name)
//    val fieldNames = for (f <- fields) yield {
//      f.name.getOrElse(f.loType.mangledName)
//    }
//    fieldNames.foldLeft("rec") { (str, f) => s"${str}_${f}" }
    Record.uniqueName(this)
  }

  override def toString: String = {
    val nameStr = name.map(f => s"[${f.name}]").getOrElse("")
    val fieldStr = fields.tail.foldLeft(fields.head.toString) { (s, f) => s"$s, $f" }
    s"Rec$nameStr($fieldStr)"
  }
}

/** A record in which fields are split into groups 
  *
  * This corresponds to a record in a multi-column relation.
  */
case class SplitRecord(groups: Seq[Record.Group], name: Option[Id], const: Boolean=false) extends Record {
  val fields: Seq[Record.Field] = groups.map(_.fields).flatten

  def setConst(c: Boolean): Record = this.copy(const = c)

  def mangledName: String = {
    name.map(id => return id.name)
//    val groupNames = for (g <- groups) yield {
//      val fieldNames = for (f <- g.fields) yield{
//        f.name.getOrElse(f.loType.mangledName)
//      }
//      fieldNames.foldLeft("") { (str, f) => s"${str}_${f}" }
//    }
//    groupNames.foldLeft(constPrefix+"_srec") { (str, f) => s"${str}_g_$f" }
    Record.uniqueName(this)
  }

  override def toString: String = {
    val nameStr = name.map(n => s"[$n]").getOrElse("")
    s"Record$nameStr(${groups.mkString(", ")})"
  }

}

object SplitRecord {
  def apply(groups: Record.Group*): SplitRecord = {
    SplitRecord(groups, None, false)
  }
}

object Record {
  /** A single field or attribute of a [[Record]] type. */
  case class Field(loType: NonRec, name: Option[Id]=None) {
    override def toString: String = {
      name match {
        case Some(id) => s"[${id.name} : $loType]"
        case None => s"[${loType.toString}]"
      }
    }
    val const = loType.const
    def mangledName = name.getOrElse("") + s"_${loType.mangledName}"
    def setConst(c: Boolean) = this.copy(loType = loType.setConst(c))
  }

  /** An extent of contiguous (row-major) fields in a [[Record]] */
  case class Group(fields: Field*) {
    override def toString: String = {
      s"{${fields.mkString(", ")}}"
    }
  }

  /** Returns an anonymous record with the given fields
    *
    * Note that the implicit method [[ressort.hi.anonymousField]] in the
    * [[ressort.hi]] package, and [[ressort.lo.anonymousField]] in the
    * [[ressort.lo]] package will produce non-named fields for [[NonRec]]
    * [[LoType]]s when given as arguments.
    */
  def apply(fields: Field*): FlatRecord = {
    FlatRecord(fields, None, false)
  }

  /** Generates and stores unique names for record type */
  object uniqueName {
    private var count = 0
    private val types = HashMap[Record, String]()
    def apply(recType: Record): String = {
      types.get(recType).map(return _)
      val name = s"_rec${count}"
      count += 1
      types(recType) = name
      name
    }
  }
}
