// See LICENSE.txt
package ressort.compiler.cpp
import ressort.lo.compiler.LoResCompiler
import ressort.lo
import ressort.util._

abstract class CppType(val name: String) {
  val const: Boolean

  override def toString = if (const) "const "+name else name

  def nonContainerErr = "C++ type "+this+" is not a container"
  def nonRangeCppTypeErr = "C++ type "+this+" does not support ranges"

  def getNumEntries(e: Expr): Expr = {
    throw new AssertionError(nonContainerErr)
  }
  def subsc(lval: Expr, n: Expr): Expr = {
    throw new AssertionError(nonContainerErr)
  }
  def bitRange(e: Expr, msb: Expr, lsb: Expr): Expr = {
    throw new AssertionError(nonRangeCppTypeErr)
  }
}

object CppType {
  def noCppTypeErr(t: lo.LoType) = "No corresponding C++ type for LoType "+t
  def apply(t: lo.LoType): CppType = t match {
    case lo.LoInt(c) => IntT(c)
    case lo.UInt(c) => UintT(c)
    case lo.Index(c) => SizeT(c)

    case lo.UInt8(c) => Uint8(c)
    case lo.UInt16(c) => Uint16(c)
    case lo.UInt32(c) => Uint32(c)
    case lo.UInt64(c) => Uint64(c)

    case lo.LoInt8(c) => Int8(c)
    case lo.LoInt16(c) => Int16(c)
    case lo.LoInt32(c) => Int32(c)
    case lo.LoInt64(c) => Int64(c)

    case lo.LoFloat(c) => Float(c)
    case lo.LoDouble(c) => Double(c)

    case a @ lo.Arr(t1, c) => Vector(this(t1), c)
    case lo.Ptr(loType, c) => Ptr(this(loType), c)
    case lo.Bool(c) => Bool(c)
    case lo.Struct(name, fields, const) => {
      val newFields = fields map { case (v,t) => (v.name->this(t)) }
      Struct(name.name, newFields, const)
    }
    case tr: lo.TypeRef => TypeRef(tr.name.name, tr.const)
    case other => throw new AssertionError(noCppTypeErr(other))
  }
}


case class Struct(
    structName: String,
    members: Seq[(String, CppType)],
    const: Boolean=false) extends CppType("struct "+structName) {

  def declare = {
    StructDec(structName, members)
  }
}

case class TypeRef(typeName: String, const: Boolean=false) extends CppType(typeName)

abstract class CppIntType(name: String) extends CppType(name) {
  override def bitRange(e: Expr, msb: Expr, lsb: Expr): Expr =  {
    val one = Const(1)
    val len = Minus(Plus(msb, one), lsb)
    val bitmask = Minus(LeftShift(one, len), one)
    BitAnd(RightShift(e, lsb), bitmask)
  }
}

case class IntT(const: Boolean=false) extends CppIntType("int")
case class UintT(const: Boolean=false) extends CppIntType("unsigned int")
case class SizeT(const: Boolean=false) extends CppIntType("size_t")

case class Uint8(const: Boolean=false) extends CppIntType("uint8_t")
case class Uint16(const: Boolean=false) extends CppIntType("uint16_t")
case class Uint32(const: Boolean=false) extends CppIntType("uint32_t")
case class Uint64(const: Boolean=false) extends CppIntType("uint64_t")

case class Int8(const: Boolean=false) extends CppIntType("int8_t")
case class Int16(const: Boolean=false) extends CppIntType("int16_t")
case class Int32(const: Boolean=false) extends CppIntType("int32_t")
case class Int64(const: Boolean=false) extends CppIntType("int64_t")


case class Ptr(
    base: CppType, 
    const: Boolean=false,
    declspec: String = "") 
  extends CppType(base+"*"+declspec) {
  
  override def subsc(lval: Expr, n: Expr) = {
    Subsc(lval, n)
  }
}
case class Bool(const: Boolean=false) extends CppType("bool")
case class Double(const: Boolean=false) extends CppType("double")
case class Float(const: Boolean=false) extends CppType("float")
case object Void extends CppType("void") { val const = false }
case class Arr(t: CppType, const: Boolean=false) extends CppType(t.toString) {
  override def subsc(lval: Expr, n: Expr) = Subsc(lval, n)
}
case class Vector(t: CppType, const: Boolean=false) extends CppType(s"res_vec<$t>") {
  override def subsc(lval: Expr, n: Expr) = Subsc(lval, n)
  override def getNumEntries(e: Expr): Expr = {
    Call(Dot(e, "size"), Nil)
  }
}
case class TemplateT(tname: String, const: Boolean=false) extends CppType(tname)
