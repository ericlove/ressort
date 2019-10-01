// See LICENSE.txt
package ressort.compiler.cpp
import ressort.lo.compiler._
import ressort.lo
import ressort.util._
import ressort.lo.compiler._

object TmpId {
  var count = 0
  val pfx = "_CTMP"
  def apply(name: String): Id = {
    count += 1
    Id(pfx+count+"_"+name)
  }
}

abstract class CppAst {
  def lines: List[String]

  def indent(l: List[String]): List[String] = { l map { "  "+_ } }

  def braces = {("{"::(indent(lines) ++ List("}")))}

  final override def toString = {
    throw new AssertionError("Call lines instead!")
  }
}
abstract class SimpleStmt extends CppAst {
  override def braces = "{"::("  "+lines(0)+";")::"}"::Nil
}


case object Nop extends CppAst {
  def lines = Nil
}

case class Comment(text: String) extends CppAst {
  def lines = List("// "+text)
}

case class Block(body: List[CppAst]) extends CppAst {
  def lines = {
    def lineList(s: CppAst) = s match {
      case simple: SimpleStmt => List(simple.lines(0)+";")
      case _ => s.lines
    }
    val bodyLineLists = body map lineList
    val bodyLines = bodyLineLists.foldLeft(List[String]()) { _ ++ _ }
    bodyLines
  }
}

case class Dec(i: Id, t: CppType, initVal: Option[Expr]) extends SimpleStmt {
  def lines = {
    val init = initVal match {
      case Some(e) => " = " + e
      case None => ""
    }
    List(t + " " + i + init)
  }
}

case class StructDec(
    name: String,
    members: Seq[(String, CppType)],
    methods: Map[Id, Func]=Map()) extends CppAst {
  def lines = {
    val top = "struct "+name+" {"
    val middle = members.toList.map { case (id, ctype) => ctype+" "+id+";" }
    val funcs = (methods.toList.map { case (id, func) => func.lines }).flatten
    top::indent(middle):::indent(funcs):::List("};\n")
  }
}

case class ClassDec(
    name: Id,
    fields: Seq[(Id, CppType)],
    methods: Seq[(Id, Func)],
    constructor: CppAst)
  extends CppAst {

  def lines = {
    val top = List(s"class $name", "{", "  public:")
    val fieldLines = fields map { case (id, cppt) => s"    $cppt $id;" }
    val constructorLines = indent(indent(List(s"$name () {") ++ indent(constructor.lines) ++ List("}")))
    val methodLines = methods map { case (id, func) => indent(indent(func.lines)) }
    top ++ fieldLines ++ constructorLines ++ methodLines.flatten ++ List("};")
  }
}

case class Assign(lval: Expr, e: Expr) extends SimpleStmt {
  override def lines = List(lval + " = " + e)
}

case class Prefetch(lval: Expr) extends SimpleStmt {
  // Only works in GCC, and some translators will want to replace with
  // an inline assembly instruction (RISC-V in particular).
  override def lines = List(s"__builtin_prefetch($lval)")
}

case class IfElse(cond: Expr, 
  ifBody: CppAst,
  elseBody: Option[CppAst] = None) extends CppAst {
  override def lines = {
    val top = "if(" + cond + ")"
    (top :: ifBody.braces) ++ (elseBody match {
        case Some(stmt) => "else"::stmt.braces
        case None => Nil
      })
  }
}

case class For(init: CppAst, cond: Expr, stride: CppAst, body: CppAst) extends CppAst {
  assert(stride.lines.length < 2)
  assert(init.lines.length < 2)
  override def lines = {
    val top = "for(" + init.lines(0) + "; " + cond + "; " + stride.lines(0) + ")"
    top::body.braces
  }
}

case class While(cond: Expr, body: CppAst) extends CppAst {
  override def lines = {
    val top = "while("+cond+")"
    top::body.braces
  }
}

case class Func(
    name: Id, 
    retCppType: CppType, 
    params: Seq[(Id, CppType)],
    body: CppAst,
    templateTypes: List[TemplateT] = Nil) extends CppAst {
  override def lines = {
    val templateLine = Func.templateDec(templateTypes)
    val top = { 
      retCppType+" "+name+
      "("+paramStr(params map { p => p._2+" "+p._1 })+")"
    }
    templateLine::top::(body.braces)
  }
}

object Func {
  def templateDec(templateTypes: List[TemplateT]): String = {
    val types = templateTypes match {
      case Nil => ""
      case head::Nil => s"typename $head"
      case head::tail => tail.foldLeft(s"typename $head") {
        (str, t) => str + s", typename $t"
      }
    }
    if (!templateTypes.isEmpty)
      s"template <$types>"
    else
      ""
  }
}

case class FuncPrototype(
    name: Id,
    retCppType: CppType,
    params: Seq[(Id, CppType)],
    templateTypes: List[TemplateT]) extends CppAst {
  override def lines = {
    List(
      Func.templateDec(templateTypes),
      (retCppType+" "+name+
        "("+paramStr(params map { p => p._2+" "+p._1 })+");"))
  }
}

case class CallStmt(call: Call) extends SimpleStmt {
  override def lines = List(call.toString)
}

case class Return(e: Expr) extends SimpleStmt {
  override def lines = List("return "+e)
}

case class Free(e: Expr) extends SimpleStmt {
  override def lines = List("delete "+e)
}

case class ArrFree(e: Expr) extends SimpleStmt {
  override def lines = List("delete[] "+e)
}

case class Printf(fmt: String, exprs: Expr*) extends SimpleStmt {
  override def lines = {
    val commaStrs = exprs.toList match {
      case h::Nil => ", "+h
      case h::t => exprs.foldLeft("") {
        case (str, e) => str + ", " + e
      }
      case Nil => ""
    }
    List("printf("+escape(fmt+"\\n")+commaStrs+")")
  }
}


/** C++ `#pragma` directive. 
  * 
  * @param content  C++ code string following `#pragma` directive
  * @param body     C++ code block over which this pragma applies
  */
case class Pragma(content: String, body: CppAst) extends CppAst {
  def pragmaLine = s"#pragma $content"

  def bodyLines = body match {
    case f: For => f.lines
    case other => other.braces
  }

  def lines = {
    pragmaLine :: bodyLines
  }
}


abstract class Expr {
  def parens = "("+this+")"
  def vparens: String = this match {
    case Id(name) => name
    case Dot(e1, e2) => e1.vparens+"."+e2
    case e => e.parens
  }
}
object Expr {
  def apply(e: lo.TypedExpr)(implicit ast: lo.TypedLoAst): Expr = {
    implicit def toTypedExpr(e1: lo.Expr): lo.TypedExpr = {
      e.scope(e1)
    }
    def transSubsc(lval: lo.LValue, n: lo.Expr) = {
      CppType(lval.loType).subsc(this(lval), this(n))
    }
    def transSize(loType: lo.LoType): Expr = {
      Sizeof(CppType(loType))
    }
    def transLWRange(e1: lo.Expr, start: lo.Expr, end: lo.Expr): Expr = {
      val newStart = Expr(start)
      val newEnd = Expr(end)
      val cppType = CppType(e.scope(e1).loType)
      cppType match {
        case int: CppIntType => {
          int.bitRange(this(e1), newEnd, newStart)
        }
        case t => {
          val loType = e.scope(e1).loType
          val err = s"Cannot extract bits from type $t (loType $loType)."
          throw new Error(err)
        }
      }
    }
    try {
      e.expr match {
        case lo.Id(name) => Id(name)
        case lo.Plus(e1, e2) => Plus(this(e1), this(e2))
        case lo.Minus(e1, e2) => Minus(this(e1), this(e2))
        case lo.Mul(e1, e2) => Mul(this(e1), this(e2))
        case lo.Div(e1, e2) => Div(this(e1), this(e2))
        case lo.Mod(e1, e2) => Mod(this(e1), this(e2))
        case lo.Neg(e) => Neg(this(e))
        case lo.Const(n) => Const(n)
        case lo.FloatConst(n) => FloatConst(n)
        case lo.DoubleConst(n) => DoubleConst(n)
        case lo.True => True
        case lo.False => False
        case lo.Greater(e1, e2) => Gt(this(e1), this(e2))
        case lo.GreaterEq(e1, e2) => GtEq(this(e1), this(e2))
        case lo.LessEq(e1, e2) => LtEq(this(e1), this(e2))
        case lo.Less(e1, e2) => Lt(this(e1), this(e2))
        case lo.Equal(e1, e2) => Eq(this(e1), this(e2))
        case lo.And(e1, e2) => And(this(e1), this(e2))
        case lo.Or(e1, e2) => Or(this(e1), this(e2))
        case lo.Not(e) => Not(this(e))
        case lo.Mux(cond, e1, e2) => Mux(this(cond), this(e1), this(e2))
        case lo.NumEntries(e) => {
          val cppCppType = CppType(e.loType)
          cppCppType.getNumEntries(this(e))
        }
        case lo.Size(te) => transSize(te)
        case lo.UField(e, n, _) => {
          throw new AssertionError(s"RecStructs transform failed to remove $e")
        }
        case lo.LowerWord(lo.BitRange(e1, start, end)) => transLWRange(e1, start, end)
        case lo.LowerWord(e) => Cast(this(e),Uint32(true))
        case lo.Log2Up(e) => {
          val dbl = Cast(this(e),Double(true))
          val log = Log2Up(dbl)
          Cast(log, IntT(true))
        }
        case lo.BitRange(e1, msb, lsb) => {
          CppType(e.loType).bitRange(this(e1), msb=this(msb), lsb=this(lsb))
        }
        case lo.ShiftLeft(e1, e2) => LeftShift(this(e1), this(e2))
        case lo.ShiftRight(e1, e2) => RightShift(this(e1), this(e2))
        case lo.Subsc(lval,n) => transSubsc(lval, n)
        case lo.Ref(lval) => Ref(this(lval))
        case lo.Deref(lval) => Deref(this(lval))
        case lo.Pow(e1, e2) => Pow(this(e1), this(e2))
        case lo.Pow2(exp) => LeftShift(Const(1), this(exp))
        case lo.Field(lo.Deref(lval), v) => DerefDot(this(lval), v.name)
        case lo.Field(l, v) => Dot(this(l), v.name)
        case lo.Cast(e, t) => Cast(this(e), CppType(t))
        case lo.FakeUse(e) => this(e)
        case lo.Safe(e) => this(e)
        case lo.Null => Null
        case lo.BitAnd(e1, e2) => BitAnd(this(e1), this(e2))
        case _ => {
          val err = "\n[C++ LoRes Translator]: Error translating expression "+e.expr
          throw new AssertionError(err)
        }
      }
    } catch {
      case me: MatchError => {
        val err = "\n[C++ LoRes Translator]: Error translating expression "+e
        throw new AssertionError(err)
      }
    }
  }
}




abstract class BinOp(e1: Expr, e2: Expr, sign: String) extends Expr {
  override def toString = e1.vparens + sign + e2.vparens
}
abstract class UnOp(e: Expr, sign: String) extends Expr {
  override def toString = sign+"("+e.vparens+")"
}
abstract class Sym(s: String) extends Expr {
  override def toString = s
}

case class Id(name: String) extends Sym(name)
case object Null extends Sym("NULL")
case class Const(n: Long) extends Sym(n.toString)
case class FloatConst(f: scala.Float) extends Sym(s"${f}f")
case class DoubleConst(f: scala.Double) extends Sym(s"${f}")
case object True extends Sym("true")
case object False extends Sym("false")
case class Plus(e1: Expr, e2: Expr) extends BinOp(e1, e2, "+")
case class Minus(e1: Expr, e2: Expr) extends BinOp(e1, e2, "-")
case class Mul(e1: Expr, e2: Expr) extends BinOp(e1, e2, "*")
case class Div(e1: Expr, e2: Expr) extends BinOp(e1, e2, "/")
case class Mod(e1: Expr, e2: Expr) extends BinOp(e1, e2, "%")
case class Neg(e: Expr) extends UnOp(e, "-")
case class Eq(e1: Expr, e2: Expr) extends BinOp(e1, e2, "==")
case class Lt(e1: Expr, e2: Expr) extends BinOp(e1, e2, "<")
case class LtEq(e1: Expr, e2: Expr) extends BinOp(e1, e2, "<=")
case class Gt(e1: Expr, e2: Expr) extends BinOp(e1, e2, ">")
case class GtEq(e1: Expr, e2: Expr) extends BinOp(e1, e2, ">=")
case class Neq(e1: Expr, e2: Expr) extends BinOp(e1, e2, "!=")
case class And(e1: Expr, e2: Expr) extends BinOp(e1, e2, "&&")
case class Or(e1: Expr, e2: Expr) extends BinOp(e1, e2, "||")
case class Not(e: Expr) extends UnOp(e, "!")
case class Mux(cond: Expr, e1: Expr, e2: Expr) extends Expr {
  override def toString = {
    cond.vparens + " ? " + e1.vparens + " : " + e2.vparens
  }
}
case class Ref(e: Expr) extends UnOp(e, "&")
case class Deref(e: Expr) extends UnOp(e, "*")
case class Call(func: Expr, args: List[Expr]) extends Expr {
  override def toString = func.vparens + "(" + paramStr(args) + ")"
}
case class Subsc(e: Expr, n: Expr) extends Expr {
  override def toString = e.vparens + "[" + n + "]"
}
case class Dot(struct: Expr, member: String) extends Expr {
  override def toString = struct.vparens + "." + member
}
case class DerefDot(structDeref: Expr, member: String) extends Expr {
  override def toString = structDeref + "->" + member
}
case class Sizeof(t: CppType) extends Expr {
  override def toString = "sizeof("+t+")"
}
case class Cast(e: Expr, t: CppType) extends Expr {
  override def toString = "("+t+")" + e.vparens
}
case class Log2Up(e: Expr) extends Expr {
  override def toString = "ceil(log("+e+")/log(2.0))"
}
case class BitAnd(e1: Expr, e2: Expr) extends BinOp(e1, e2, "&")
case class BitOr(e1: Expr, e2: Expr) extends BinOp(e1, e2, "|")
case class BitNot(e: Expr) extends UnOp(e, "~")
case class LeftShift(e1: Expr, e2: Expr) extends BinOp(e1, e2, "<<")
case class RightShift(e1: Expr, e2: Expr) extends BinOp(e1, e2, ">>")
case class Pow(e1: Expr, e2: Expr) extends Expr {
  override def toString = {
    "pow("+e1+", "+e2+")"
  }
}
case class ArrAlloc(scalarType: CppType, len: Expr) extends Expr {
  override def toString = { "new " + scalarType + "["+len+"]" }
}
case class Alloc(cppCppType: CppType, constructorArgs: Seq[Expr]=Nil) extends Expr {
  override def toString = {
    if (constructorArgs.nonEmpty) {
      val args = constructorArgs.mkString(", ")
      s"new $cppCppType($args)"
    } else {
      s"new $cppCppType"
    }
  }
}
case class ReinterpretCast(newType: CppType, e: Expr) extends Expr {
  override def toString = s"reinterpret_cast<$newType>($e)"
}

