// See LICENSE.txt
package ressort.lo
import ressort.hi
import ressort.lo.compiler.ReplaceExprs
import ressort.util._
import ressort.lo.interp.EVal

import scala.collection.mutable.ArrayBuffer

/** Abstract Syntax Tree (AST) for the LoRes intermediate language. */
sealed abstract class LoAst {
  def +(o2: LoAst): Block = (this, o2) match {
    case (Nop, Nop) => Block(Nil)
    case (Block(l), Nop) => Block(l)
    case (_, Nop) => Block(this::Nil)
    case (Nop, Block(l)) => Block(l)
    case (Nop, _) => Block(o2::Nil)
    case (Block(l), _) => Block(l ++ (o2::Nil))
    case (_, _) => Block(this::o2::Nil)
  }
  
  val tabstop = "  "

  /** Adds this AST's textual representation to `listing` and returns the lines to which it belongs */
  def lines(indent: Integer=0, listing: LoAstListing = new LoAstListing()): LoAstLines = {
    val start = listing.length
    val ind = tabstop * indent
    listing += ind + toString
    LoAstLines(this, start = start, end = start, children = Nil, listing = listing)
  }

  /** Returns a stringification of this AST indented `n` tabstops */
  def tabStr(n: Integer): String = lines(n).listing.toString

  def toApp: App = throw new AssertionError(this+" is not an App()")
  def toFuncDec: FuncDec = throw new AssertionError(this+" is not a FuncDec()")

  /** Returns a list of all [[Expr]] child nodes of this [[LoAst]]. 
    *
    * Results must appear in the linear order in which they occur in
    * this AST node's constructor.
    */
  def exprChildren: List[Expr] = Nil

  /** Returns a list of all this node's [[LoAst]] children.
    *
    * Results must appear in the linear order in which they occur in
    * this node's constructor.
    */
  def astChildren: List[LoAst] = Nil

  /** Returns a modified version of this AST node where all child AST nodes
    * have been replaced by their corresponding nodes in `newChildren`
    *
    * @note The ndoes in `newChidlren` must appear in the same linear order
    *       in their original counterparts appear in this AST's constructor.
    */
  def replaceAstChildren(newChildren: List[LoAst]): LoAst = this

  /** Returns a modified version of this AST node where all child expressions
    * have been replaced by their corresponding nodes in `newChildren`
    *
    * @note The ndoes in `newChidlren` must appear in the same linear order
    *       in their original counterparts appear in this AST's constructor.
    */
  def replaceExprChildren(newChildren: List[Expr]): LoAst = this
}

/** A textual representation of a `LoRes` AST */
class LoAstListing {
  private val lines = ArrayBuffer[String]()
  private var nextLine = 0
  private var string: Option[String] = None

  def length: Integer = nextLine

  def +=(line: String): Unit = {
    lines += line
    nextLine += 1
    string = None
  }

  override def toString: String = {
    string.map(return _)
    string = Some(range(0, lines.length-1))
    string.get
  }

  /** Returns a string of the lines from `start` to `end` inclusive */
  def range(start: Integer, end: Integer): String = {
    val b = new StringBuilder()
    for (i <- scala.collection.immutable.Range(start, end+1)) {
      b ++= "% 3d: ".format(i)
      b ++= lines(i)
      b += '\n'
    }
    b.toString
  }
}

case class LoAstLines(
    ast: LoAst,
    start: Integer,
    end: Integer,
    children: List[LoAstLines],
    listing: LoAstListing) {
  override def toString = listing.range(start, end)
}
case object Nop extends LoAst

abstract class FakeLoAst extends LoAst

case class Block(ops: List[LoAst]) extends LoAst {
  override def lines(indent: Integer=0, listing: LoAstListing = new LoAstListing()): LoAstLines = {
    val start = listing.length
    val clines = ops.map(_.lines(indent+1, listing))
    val end = listing.length - 1
    LoAstLines(this, start = start, end = end, children = clines, listing = listing)
  }

  override def astChildren = ops

  override def replaceAstChildren(newChildren: List[LoAst]): Block = {
    Block(newChildren)
  }
}

/** An AST node that declares an ID visible in subsequent scope.
  *
  * Allows [[Dec]] and [[DecAssign]] to be treated identically by AST
  * manipulation routines.
  */
trait DecLike {
  /** Symbol being declared */
  def sym: SymLike

  /** Type of the symbol being declared */
  def loType: LoType
}

/** An AST node whose purpose is to update an LValue 
  *
  * Allows all ''write''-like operations to be treated identically by
  * AST manipulation routines.
  */
trait LValueUpdate {
  /** LValue being updated */
  def lhs: LValue
}

/** An AST node that assigns a new value to an LValue from an expression
  *
  * Allows [[Assign]] and [[DecAssign]] to be treated identically by AST
  * manipulation routines.
  */
trait AssignLike extends LValueUpdate {
  /** LValue being assigned to */
  def lhs: LValue

  /** Expression being assigned to an LValue */
  def rhs: Expr
}

case class Dec(v: SymLike, loType: LoType) extends LoAst with DecLike {
  override def toString() : String = {
    "var " + v + ": " + loType.mangledName
  }

  // Needed for `DecLike` trait
  def sym = v
}

case class Assign(l:LValue, e: Expr) extends LoAst with AssignLike {
  override def toString() : String = e match {
    case Safe(e1) => s"$l [:=] $e1"
    case _ => s"$l := $e"
  }
  override def exprChildren = List(l, e)

  override def replaceExprChildren(newChildren: List[Expr]): LoAst = {
    copy(l = newChildren(0).toLValue, newChildren(1))
  }

  val lhs = l

  val rhs = e
}

case class Prefetch(l: LValue) extends LoAst with LValueUpdate {
  override def exprChildren = List(l)

  override def replaceExprChildren(newChildren: List[Expr]): LoAst = {
    copy(l = newChildren.head.toLValue)
  }

  // Needed for LValueUpdate trait
  val lhs = l
}

case class DecAssign(
    sym:    SymLike,
    loType: LoType,
    value:  Expr)
  extends DecAssignLike with AssignLike with DecLike {

  override def replaceExprChildren(newChildren: List[Expr]): DecAssign = {
    copy(value = newChildren.head)
  }
}

trait DecAssignLike extends LoAst with DecLike with AssignLike {
  def sym:    SymLike
  def loType: LoType
  def value:  Expr

  override def toString(): String = {
    val vc = if (loType.const) "const" else "var"
    s"$vc ${sym}: ${loType.mangledName} := $value"
  }
  override def exprChildren = List(value)


  // Needed to satisfy the [[AssignLike]] trait
  val lhs = sym
  val rhs = value
}

object Increment {
  def apply(lv: LValue, amount: Expr=Const(1)) = {
    Assign(lv, lv + amount)
  }
}

case class HeapAlloc(l: LValue, length: Option[Expr]=None) extends LoAst with LValueUpdate {
  override def toString() : String = {
    val lstr = length.map(l => s", $l").getOrElse("")
    s"Alloc [ $l$lstr ]"
  }
  override def exprChildren = List(Some(l), length).flatten

  override def replaceExprChildren(newChildren: List[Expr]): HeapAlloc = {
    val newLen = if (newChildren.length > 1) Some(newChildren(1)) else None
    copy(l = newChildren.head.toLValue, length = newLen)
  }

  // Needed for LValueUpdate trait
  val lhs = l
}


case class Free(l: LValue) extends LoAst with LValueUpdate {
  override def exprChildren = List(l)

  override def replaceExprChildren(newChildren: List[Expr]): Free = {
    copy(l = newChildren.head.toLValue)
  }

  // Needed for LValueUpdate trait
  val lhs = l
}

case class AssignReturn(l: LValue, a: App) extends LoAst with LValueUpdate {
  override def toString(): String = {
    l + " := " + a
  }
  override def exprChildren = List(l)
  override def astChildren = List(a)

  override def lines(indent: Integer, listing: LoAstListing): LoAstLines = {
    super.lines(indent, listing).copy(children = List(Nop.lines(indent, listing)))
  }

  override def replaceAstChildren(newChildren: List[LoAst]): AssignReturn = {
    AssignReturn(l, newChildren.head.asInstanceOf[App])
  }

  override def replaceExprChildren(newChildren: List[Expr]): LoAst = {
    copy(l = newChildren.head.toLValue)
  }

  // Needed for LValueUpdate trait
  val lhs = l
}

case class Typedef(struct: Struct) extends LoAst {
  def fields = struct.fields
  def name = struct.name

  override def lines(indent: Integer=0, listing: LoAstListing = new LoAstListing()): LoAstLines = {
    val start = listing.length
    val ind = tabstop * indent
    listing += s"${ind}Typedef ${struct.name} {"
    val fieldLines = fields map {
      case (v, te) => listing += s"$ind$tabstop$v : ${te.mangledName}"
    }
    listing += s"$ind}"
    val end = listing.length - 1
    LoAstLines(this, start = start, end = end, children = Nil, listing = listing)
  }

  override def equals(o: Any): Boolean = o match {
    case Typedef(Struct(name, fields, _)) => name == this.name
    case _ => false
  }

  override def hashCode = name.hashCode
}

/** LoRes For Loops.
  *
  * The only difference from a C loop is that all bound expressions
  * (`min`, `max`, and `stride`) are ''pre-computed'' once before the
  * body is executed, and retain their constant values across all
  * iterations.
  */
abstract class ForLoopLoAst extends LoAst {
  /** Loop induction variable */
  val index: SymLike

  /** Loop lower bound (inclusive) */
  val min: Expr

  /** Loop upper bound (exclusive) */
  val max: Expr   

  /** Amount by which loop index incremented between 
    * iterations.
    */
  val stride: Expr
  
  val body: LoAst

  /** Either "For" or "ForPar" depending on which type of loop this is */
  val forName: String

  override def astChildren = List(body)
  override def exprChildren = List(min, max, stride)
  def withIndex(index: SymLike): ForLoopLoAst
  def withBody(body: LoAst): ForLoopLoAst

  override def lines(indent: Integer=0, listing: LoAstListing = new LoAstListing()): LoAstLines = {
    val start = listing.length
    val ind = tabstop * indent
    listing += s"$ind$forName(${index} = $min...$max by $stride) {"
    val children = body.lines(indent+1, listing) :: Nil
    val end = listing.length
    listing += s"$ind}"
    LoAstLines(this, start = start, end = end, children = children, listing = listing)
  }
}

/** Parallel for loop 
  *
  * Semantics similar to OpenMP parallel for: loop iterations must
  * have no inter-dependencies and must be able to be executed in any
  * order or concurrently.
  */
case class ForPar(
    index:  SymLike,
    min:    Expr,
    max:    Expr, 
    stride: Expr,
    body:   LoAst) extends ForLoopLoAst {

  val forName = "ForPar"

  override def replaceAstChildren(newChildren: List[LoAst]): ForPar = {
    this.copy(body = newChildren.head)
  }
  override def replaceExprChildren(newChildren: List[Expr]): LoAst = {
    ForPar(
      index = index,
      min = newChildren(0),
      max = newChildren(1),
      stride = newChildren(2),
      body = body)
  }
  def withIndex(index: SymLike) = copy(index = index)
  def withBody(body: LoAst) = copy(body = body)
}

/** Sequential For Loop */
case class ForSeq(
    index:  SymLike,
    min:    Expr,
    max:    Expr, 
    stride: Expr,
    body:   LoAst) extends ForLoopLoAst {

  val forName = "For"

  override def replaceAstChildren(newChildren: List[LoAst]): ForSeq = {
    this.copy(body = newChildren.head)
  }
  override def replaceExprChildren(newChildren: List[Expr]): LoAst = {
    ForSeq(
      index = index,
      min = newChildren(0),
      max = newChildren(1),
      stride = newChildren(2),
      body = body)
  }
  def withIndex(index: SymLike) = copy(index = index)
  def withBody(body: LoAst) = copy(body = body)
}

/** Syntactic sugar to emulate previous `ForBlock` format */
object ForBlock {
  def apply(index: SymLike, n: Expr, body: LoAst): LoAst = {
    ForSeq(index, min=0, max=n, stride=1, body=body)
  }
}

/** Syntactic sugar to emulate previous `IPar` format */
object IPar {
  def apply(index: SymLike, n: Expr, body: LoAst): LoAst = {
    ForPar(index, min=0, max=n, stride=1, body)
  }
}

case class While(cond: Expr, body: LoAst) extends LoAst {
  override def lines(indent: Integer=0, listing: LoAstListing = new LoAstListing()): LoAstLines = {
    val start = listing.length
    val ind = tabstop * indent
    listing += s"${ind}While($cond) {"
    val children = body.lines(indent+1, listing) :: Nil
    val end = listing.length
    listing += s"$ind}"
    LoAstLines(this, start = start, end = end, children = children, listing = listing)
  }

  override def exprChildren = List(cond)
  override def astChildren = List(body)

  override def replaceAstChildren(newChildren: List[LoAst]): While = {
    this.copy(body = newChildren.head)
  }

  override def replaceExprChildren(newChildren: List[Expr]): While = {
    this.copy(cond = newChildren.head)
  }
}

object If {
  def apply(cond: Expr, body: LoAst): LoAst = {
    IfElse(cond, body, Nop)
  }
}

case class IfElse(cond: Expr, ifBody: LoAst, elseBody: LoAst) extends LoAst {
  override def lines(indent: Integer=0, listing: LoAstListing = new LoAstListing()): LoAstLines = {
    val start = listing.length
    val ind = tabstop * indent
    listing += s"${ind}If ($cond) {"
    val ifLines = ifBody.lines(indent + 1, listing)
    val children = if (elseBody != Nop) {
      listing += s"${ind}} else {"
      val elseLines = elseBody.lines(indent + 1, listing)
      List(ifLines, elseLines)
    } else {
      List(ifLines, Nop.lines(indent+1, listing))
    }
    val end = listing.length
    listing += s"$ind}"
    LoAstLines(this, start = start, end = end, children = children, listing = listing)
  }

  override def exprChildren = List(cond)
  override def astChildren = List(ifBody, elseBody)

  override def replaceAstChildren(newChildren: List[LoAst]): IfElse = {
    assert(newChildren.length == 2)
    IfElse(cond, newChildren(0), newChildren(1))
  }

  override def replaceExprChildren(newChildren: List[Expr]): IfElse = {
    this.copy(cond = newChildren.head)
  }
}

case class OutputMatch(tup1: Expr, tup2: Expr) extends LoAst {
  override def exprChildren = List(tup1, tup2)

  override def replaceExprChildren(newChildren: List[Expr]): OutputMatch = {
    copy(tup1 = newChildren(0), tup2 = newChildren(1))
  }
}

case class Printf(fmt: String, e: Expr*) extends LoAst {
  override def toString: String = {
    val exprs = e.toList match {
      case Nil => ""
      case nonEmpty => {
        nonEmpty.foldLeft("") { (str, e) => str + ", " + e }
      }
    }
    "Printf("+escape(fmt) + exprs + ")"
  }
  override def exprChildren = e.toList

  override def replaceExprChildren(newChildren: List[Expr]): Printf = {
    Printf(fmt = fmt, e = newChildren:_*)
  }
}

/** Function declaration.
  *
  * LoRes functions use pass by value semantics (application has an implicit 
  * block of "assign" statements).  As in C, functions create an isolated local
  * type environment on top of Symtab.Empty, but unlike in C, they can be nested.
  */
case class FuncDec(
    name: Id, 
    params: Seq[(Id, Primitive)],
    body: LoAst,
    returnType: Option[Primitive] = None) extends LoAst {
  override def lines(indent: Integer=0, listing: LoAstListing = new LoAstListing()): LoAstLines = {
    val start = listing.length
    val ind = tabstop * indent
    listing += s"${ind}Func $name ("
    for (p <- params) {
      listing += s"$ind$tabstop$tabstop${p._1} : ${p._2.mangledName}"
    }
    val returnTypeStr = returnType match {
      case Some(loType) => loType.mangledName
      case _ => ""
    }
    listing += s"$ind) : $returnTypeStr {"
    val children = List(body.lines(indent+1, listing))
    val end = listing.length
    listing += s"$ind}"
    LoAstLines(this, start = start, end = end, children = children, listing = listing)
  }

  override def toFuncDec: FuncDec = this

  override def astChildren = List(body)
 
  override def replaceAstChildren(newChildren: List[LoAst]): FuncDec = {
    this.copy(body = newChildren.head)
  }
}

case class App(func: Id, args: Seq[(Id, Expr)]) extends LoAst {
  override def toString(): String = {
    val argStr = paramStr(args.map { case (v, e) => v+"="+e })
    func+"("+argStr+")"
  } 
  override def toApp: App = this

  override def exprChildren = args.map(_._2).toList

  override def replaceExprChildren(newChildren: List[Expr]): App = {
    copy(args = args.zip(newChildren).map(a => a._1._1 -> a._2))
  }
}

case class Return(expr: Expr) extends LoAst {
  override def exprChildren = List(expr)

  override def replaceExprChildren(newChildren: List[Expr]): Return = {
    copy(newChildren.head)
  }
}

/** Introduces a dataflow relationship from `input` to `observer`.
  *
  * This can be used to "trick" the DCE and SSA passes when temporary pointer aliasing
  * is known to occur.
  *
  * @param observer The symbol to which data flows
  * @param input The symbol "seen by" the `obersver`
  */
case class UseSym(observer: SymLike, input: SymLike) extends LoAst {
  override def exprChildren: List[Expr] = List(observer, input)
  override def replaceExprChildren(newChildren: List[Expr]): UseSym = {
    copy(newChildren(0).asInstanceOf[SymLike], newChildren(1).asInstanceOf[SymLike])
  }
}

/** Array Operations:
  *
  * Array operations (`ArrOp`s) perform some primtivive operation over a
  * whole array or some sub-array.  LoRes encodes these explicitly so that
  * backends can translate them into the most efficient implementations.
  */
sealed abstract class ArrOp(
    val opArr: LValue, 
    val opRange: Option[ArrOpRange],
    otherExprs: List[Expr] = Nil)
  extends LoAst with LValueUpdate {

  override def exprChildren = {
    val rangeExprs = opRange.map{r => r.start::r.end::Nil} getOrElse Nil
    (opArr :: otherExprs) ++ rangeExprs
  }

  val lhs = opArr
}

/** Indices of first and last elements (inclusive) respectively ove
  * over which to apply an [[ArrOp]].
  */
case class ArrOpRange(start: Expr, end: Expr) {
  def replaceExprs(newExprs: List[Expr]): ArrOpRange = {
    copy(start = newExprs(0), end = newExprs(1))
  }
}


case class RotLeft(
    arr: LValue, 
    shamt: Expr, 
    range: Option[ArrOpRange]) extends ArrOp(arr, range, shamt::Nil) {

  override def replaceExprChildren(newChildren: List[Expr]): RotLeft = {
    this.copy(
      arr = newChildren.head.toLValue,
      shamt = newChildren(1),
      range.map(_.replaceExprs(newChildren.drop(2))))
  }
}
case class RotRight(
    arr: LValue, 
    shamt: Expr, 
    range: Option[ArrOpRange]) extends ArrOp(arr, range, shamt::Nil) {

  override def replaceExprChildren(newChildren: List[Expr]): RotRight = {
    this.copy(
      arr = newChildren.head.toLValue,
      shamt = newChildren(1),
      range.map(_.replaceExprs(newChildren.drop(2))))
  }
}
case class Reverse(
    arr: LValue, 
    range: Option[ArrOpRange]) extends ArrOp(arr, range) {

  override def replaceExprChildren(newChildren: List[Expr]): Reverse = {
    this.copy(
      arr = newChildren.head.toLValue,
      range.map(_.replaceExprs(newChildren.drop(1))))
  }
}
case class PrefixSum(
    arr: LValue, 
    range: Option[ArrOpRange]) extends ArrOp(arr, range) {

  override def replaceExprChildren(newChildren: List[Expr]): PrefixSum = {
    this.copy(
      arr = newChildren.head.toLValue,
      range.map(_.replaceExprs(newChildren.drop(1))))
  }
}
case class Memset(
    arr: LValue, 
    value: Expr, 
    range: Option[ArrOpRange]) extends ArrOp(arr, range, value::Nil) {

  override def replaceExprChildren(newChildren: List[Expr]): Memset = {
    this.copy(
      arr = newChildren.head.toLValue,
      value = newChildren(1),
      range.map(_.replaceExprs(newChildren.drop(2))))
  }
}

// Just fake this one for now by translating to regular LoRes code
// TODO: Make this an ArrOp somehow?
object Memcpy {
  def apply(
      src:        LValue,
      dest:       LValue,
      srcRange:   Option[ArrOpRange] = None,
      destRange:  Option[ArrOpRange] = None) = {
    val i = Id("MEMCPY_i")
    val max = destRange match {
      case Some(ArrOpRange(start, end)) => end-start+1
      case None => NumEntries(dest)
    }
    val srcOff = srcRange.map(_.start) getOrElse Const(0)
    val destOff = destRange.map(_.end) getOrElse Const(0)
    IPar(i, max, 
      dest.sub(destOff+i) := src.sub(srcOff+i))
  }
}

/** All expressions in the LoRes grammar inherit from this base class.
  *
  * Provided features:
  *   -- Syntactic sugar for basic arith operators (+/- etc)
  *   -- Conversion functions between major categories of expression
  *       (toLValue, toConst, etc.)
  */
sealed abstract class Expr {
  def +(o: Expr): Expr = (this, o) match {
    case (_, Const(0)) => this
    case (Const(0), _) => o
    case (_, Neg(e)) if e == this => Const(0)
    case _ => Plus(this, o)
  }
  def -(o: Expr): Expr = Minus(this, o)
  def *(o: Expr): Expr = Mul(this, o)
  def /(o: Expr): Expr = Div(this, o)
  def %(o: Expr): Expr = Mod(this, o)
  def <(o: Expr): Expr = Less(this, o)
  def >(o: Expr): Expr = Greater(this, o)
  def &&(o: Expr): Expr = And(this, o)
  def ||(o: Expr): Expr = Or(this, o)
  def >=(o: Expr): Expr = GreaterEq(this, o)
  def <=(o: Expr): Expr = LessEq(this, o)
  def <<(o: Expr): Expr = ShiftLeft(this, o)
  def >>(o: Expr): Expr = ShiftRight(this, o)
  def numEntries = NumEntries(this)
  def range(start: Expr, end: Expr) = {
    BitAnd(this >> start, ((Const(1) << (end-start+Const(1)))-Const(1)))
  }
  def lowerWord = LowerWord(this)
  def log2Up = this match {
    case Pow2(e) => e
    case _ => Log2Up(this)
  }

  def toLValue: LValue = throw new AssertionError(this+" is not an LValue.")
  def toConst: Const = throw new AssertionError(this+" is not a Const.")
  def toId: Id = throw new AssertionError(this+" is not a Id.")
  def apply(start: Expr, end: Expr) = range(start, end)

  /** List of all sub-expressions contained in this one, in order they appear
    * in the case class's constructor
    */
  def children: List[Expr]

  /** This expression with `children` replaced by the given values */
  def replaceChildren(children: List[Expr]): Expr
}

object Expr {
  implicit def fromInt(n: Int): Expr = Const(n)
  implicit def makeOptionalExpr(e: Expr) = { Some(e) }

  def apply(hiExpr: hi.Expr, arraySizes: Option[hi.DagOp => Expr]=None)(implicit implicitRec: Option[(SymLike, Primitive)]=None): Expr  = {
    def trans(hiExpr: hi.Expr): Expr = {
      type BinOpMaker = (Expr, Expr) => Expr
      def binOp(e1: hi.Expr, e2: hi.Expr)(makeExpr: BinOpMaker): Expr = {
        makeExpr(trans(e1), trans(e2))
      }
      hiExpr match {
        case hi.Length(hi.IdOp(id)) =>  NumEntries(Deref(trans(id).toId))
        case hi.Plus(e1, e2) => binOp(e1, e2) { (a,b) => Plus(a, b) }
        case hi.Div(e1, e2) => binOp(e1, e2) { (a,b) => Div(a, b) }
        case hi.Mul(e1, e2) => binOp(e1, e2) { (a,b) => Mul(a, b) }
        case hi.Pow(e1, e2) => binOp(e1, e2) { (a,b) => Pow(a, b) }
        case hi.Pow2(e) => Pow2(trans(e))
        case hi.Log2Up(e) => trans(e).log2Up
        case hi.Neg(e1) => Neg(trans(e1))
        case hi.Less(e1, e2) => binOp(e1, e2) { (a,b) => Less(a, b) }
        case hi.Greater(e1, e2) => binOp(e1, e2) { (a,b) => Greater(a, b) }
        case hi.GreaterEq(e1, e2) => binOp(e1, e2) { (a,b) => GreaterEq(a, b) }
        case hi.LessEq(e1, e2) => binOp(e1, e2) { (a,b) => LessEq(a, b) }
        case hi.Equal(e1, e2) => binOp(e1, e2) { (a,b) => Equal(a, b) }
        case hi.Not(e) => Not(trans(e))
        case hi.And(e1, e2) => binOp(e1, e2) { (a,b) => And(a, b) }
        case hi.Or(e1, e2) => binOp(e1, e2) { (a,b) => Or(a, b) }
        case hi.Const(n) => Const(n)
        case hi.FloatConst(n) => FloatConst(n)
        case hi.DoubleConst(n) => DoubleConst(n)
        case hi.UField(n) => implicitRec match {
          case Some((name, rec: Record)) => UField(name, n)
          case Some((name, _)) => name
          case None => ??? // Should be caught in type check
        }
        case hi.BitRange(e, msb, lsb) => {
          val loMsb = trans(msb)
          val loLsb = trans(lsb)
          trans(e).range(start = loLsb, end = loMsb)
        }
        case hi.Id(s) => implicitRec match {
          case None => Id(s)
          case Some((name, rec: Record)) if rec.namedFields.contains(s) => {
            Field(name, Id(s))
          }
          case _ => Id(s)
        }
        case hi.Cast(e, t) => Cast(trans(e), t.loType)
        case hi.True => True
        case hi.False => False
        case hi.Length(d: hi.DagOp) => arraySizes.get.apply(d)
        case other => {
          throw new Error("Don't know how to translate HiRes expression "+other)
        }
      }
    }
    val lo = trans(hiExpr)
    val res = ReplaceExprs(lo)
    res
  }
}

sealed trait ConstExpr extends Expr

sealed abstract trait BinOp extends Expr {
  val sign: String
  val e1: Expr
  val e2: Expr

  override def toString() = {
    def addParens(e: Expr) = e match {
      case Const(_) => e.toString()
      case Id(_) => e.toString()
      case _ => "("+e+")"
    }
    addParens(e1) + sign + addParens(e2)
  }

  def children: List[Expr] = List(e1, e2)
}

case class Plus(e1: Expr, e2: Expr) extends BinOp {
  val sign = "+";
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}


case class Minus(e1: Expr, e2: Expr) extends BinOp {
  val sign = "-"
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
case class Div(e1: Expr, e2: Expr) extends BinOp {
  val sign = "/"
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
case class Mod(e1: Expr, e2: Expr) extends BinOp {
  val sign = "%"
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
case class Mul(e1: Expr, e2: Expr) extends BinOp {
  val sign = "*"
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
case class Neg(e: Expr) extends Expr {
  def children = List(e)
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
}
case class Pow(base: Expr, exp: Expr) extends BinOp {
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
  val e1 = base
  val e2 = exp
  val sign = "**"
}
case class Pow2(exp: Expr) extends Expr {
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
  def children = List(exp)
}
case class Const(n: Long) extends ConstExpr {
  override def toString() : String = { n.toString() }
  def children = Nil
  def replaceChildren(children: List[Expr]) = this
  override def +(o: Expr): Expr = o match {
    case Const(n2) => Const(n+n2)
    case FloatConst(n2) => FloatConst(n.toFloat + n2)
    case DoubleConst(n2) => DoubleConst(n.toDouble + n2)
    case _ => super.+(o)
  }
  override def -(o: Expr): Expr = o match {
    case Const(n2) => Const(n-n2)
    case FloatConst(n2) => FloatConst(n.toFloat - n2)
    case DoubleConst(n2) => DoubleConst(n.toDouble - n2)
    case _ => super.-(o)
  }
  override def *(o: Expr): Expr = o match {
    case Const(n2) => Const(n*n2)
    case FloatConst(n2) => FloatConst(n.toFloat * n2)
    case DoubleConst(n2) => DoubleConst(n.toDouble * n2)
    case _ => super.*(o)
  }
  override def /(o: Expr): Expr = o match {
    case Const(n2) => Const(n/n2)
    case FloatConst(n2) => FloatConst(n.toFloat / n2)
    case DoubleConst(n2) => DoubleConst(n.toDouble / n2)
    case _ => super./(o)
  }
  override def %(o: Expr): Expr = o match {
    case Const(n2) => Const(n%n2)
    case _ => super.%(o)
  }
  override def <(o: Expr): Expr = o match {
    case Const(n2) => BoolConst(n < n2)
    case FloatConst(n2) => BoolConst(n.toFloat < n2)
    case DoubleConst(n2)=> BoolConst(n.toDouble < n2)
    case _ => super.<(o)
  }
  override def >>(o: Expr): Expr = o match {
    case Const(n2) => Const(n >> n2)
    case _ => super.>>(o)
  }
  override def <<(o: Expr): Expr = o match {
    case Const(n2) => Const(n << n2)
    case _ => super.<<(o)
  }
  def &(o: Expr): Expr = o match {
    case Const(n2) => Const(n & n2)
    case _ => ???
  }
}
case class FloatConst(f: Float) extends ConstExpr {
  override def toString(): String = { f.toString() }
  def children = Nil
  def replaceChildren(children: List[Expr]) = this
}
case class DoubleConst(d: Double) extends ConstExpr {
  override def toString(): String = { d.toString() }
  def children = Nil
  def replaceChildren(children: List[Expr]) = this
}
case class BitRange(e: Expr, end: Expr, start: Expr) extends Expr {
  def children = List(e, start, end)
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(2), children(1)) }
}
case class BitAnd(e1: Expr, e2: Expr) extends BinOp {
  val sign = "&"
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
sealed trait Shift extends BinOp {
  val e1: Expr
  val e2: Expr
}
case class ShiftLeft(e1: Expr, e2: Expr) extends Shift {
  val sign = "<<"
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
case class ShiftRight(e1: Expr, e2: Expr) extends Shift {
  val sign = ">>"
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}

//
// L-Values 
//
sealed abstract class LValue extends Expr {
  def sub(o: Expr) = Subsc(this, o)
  def sub(i: Int) = Subsc(this, Const(i))
  def :=(o: Expr) = Assign(this, o)
  def dot(f: Id) = Field(this, f)
  def dash(f: Id) = Field(Deref(this), f)
  def lvRange(start: Expr, end: Expr) = LVRange(this, start, end)
  def root(): SymLike = this match {
    case s: SymLike => s
    case Subsc(lval, _) => lval.root()
    case Deref(lval) => lval.root()
    case Field(lval, _) => lval.root()
    case LVRange(lval, _, _) => lval.root()
    case UField(lval, _, _) => lval.root()
  }
  def withRoot(s: SymLike): LValue = this match {
    case s2: SymLike => s
    case Subsc(lval, n) => Subsc(lval.withRoot(s), n)
    case Deref(lval) => Deref(lval.withRoot(s))
    case Field(lval, f) => Field(lval.withRoot(s), f)
    case LVRange(lval, e1, e2) => LVRange(lval.withRoot(s), e1, e2)
    case UField(lval, n, id) => UField(lval.withRoot(s), n, id)
  }
  override def toLValue = this
}


sealed trait SymLike extends LValue {
  def name: String

  def :=(loType: LoType, e: Expr): LoAst = DecAssign(this, loType, e)
  def children: List[Expr] = Nil

  def symId: SymId = throw new Error("LoSym expected; found Id")
}

/** A symbol that matches on name ([[String]]) equality */
case class Id(name: String) extends SymLike {
  override def toId: Id = this
  override def toString() : String = name 
  def apply(args: (Id, Expr)*) =  App(this, args)
  def replaceChildren(children: List[Expr]) = this
}

/** Symbol replaced by an integer for faster random lookups */
case class IntSym(i: Integer) extends SymLike {
  def replaceChildren(childre: List[Expr]) = this
  def name = i.toString
}

class SymId(val name: String)

/** Like an [[Id]], but matches on reference rather than name equality
  *
  * In order to support SSA-renaming, the `n` field allows multiple 
  * versions of the underlying `symId` to be differentiated.
  * Only the SSA pass should care about the equivalence of different `n`s.
  */
case class LoSym(override val symId: SymId, n:Int=0) extends SymLike {
  def name = symId.name
  override def toString = s"LoSym($name[$n] : $symId)"
  def replaceChildren(children: List[Expr]) = this
  def next: LoSym = copy(n = n+1)
}


/** A factory for symbols */
class TempIds(prefix: String = "_t_") {
  def newId(name: String): SymLike = {
    if (TempIds.debug) {
      TempIds.count += 1
      Id(s"$prefix${name}_${TempIds.count}")
    }
    else {
      LoSym(new SymId(name))
    }
  }
}
object TempIds {
  var debug: Boolean = false
  private var count: Int = 0
}

case class Deref(l: LValue) extends LValue {
  def children = l::Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0).toLValue) }
}
case class Ref(l: LValue) extends Expr {
  def children = l::Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0).toLValue) }
}
case class LVRange(lv: LValue, start: Expr, end: Expr) extends LValue {
  def children = List(lv, start, end)
  def replaceChildren(children: List[Expr]) = { copy(children(0).toLValue, children(1), children(2)) }
}
case class Field(lv: LValue, field: Id) extends LValue {
  override def toString() = lv match {
    case Deref(l2) => s"$l2->$field"
    case _ => s"$lv.$field"
  }
  def children = List(lv)
  def replaceChildren(children: List[Expr]) = { copy(children(0).toLValue) }
}
case class UField(lv: LValue, field: Int, name: Option[Id]=None) extends LValue {
  override def toString: String = lv match {
    case Deref(l2) if name.nonEmpty => s"$l2->${name.get}"
    case _ if name.nonEmpty => s"$lv.${name.get}"
    case _ => s"$lv<$field>"
  }
  def children = List(lv)

  def replaceChildren(children: List[Expr]) = { copy(children(0).toLValue) }
}
case class Subsc(l: LValue, n: Expr) extends LValue {
  override def toString() : String = { l + "[" + n + "]" }
  def children = List(l, n)
  def replaceChildren(children: List[Expr]) = { copy(children(0).toLValue, children(1)) }
}


//
// Boolean Operators
//
case class Less(e1: Expr, e2: Expr) extends BinOp {
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
  val sign = "<"
}
case class Greater(e1: Expr, e2: Expr) extends BinOp {
  val sign = ">"
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
case class GreaterEq(e1: Expr, e2: Expr) extends BinOp {
  val sign = ">="
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
case class LessEq(e1: Expr, e2: Expr) extends BinOp {
  val sign = "<="
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
case class Equal(e1: Expr, e2: Expr) extends BinOp {
  val sign = "=="
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}

sealed trait BoolConst extends ConstExpr {
  def value: Boolean
}
object BoolConst {
  def apply(bool: Boolean) = if (bool) True else False
}
case object True extends BoolConst {
  def children = Nil
  def value = true
  def replaceChildren(children: List[Expr]) = this
}
case object False extends BoolConst {
  def children = Nil
  def value = false
  def replaceChildren(children: List[Expr]) = this
}
case class And(e1: Expr, e2: Expr) extends BinOp {
  val sign = "&&"
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
case class Or(e1: Expr, e2: Expr) extends BinOp {
  val sign = "||"
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1)) }
}
case class Not(e: Expr) extends Expr {
  def children = e::Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
}

case object Null extends ConstExpr {
  def children = Nil
  def replaceChildren(children: List[Expr]) = this
}


case class Mux(cond: Expr, e1: Expr, e2: Expr) extends Expr {
  def children = List(cond, e1, e2)
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1), children(2)) }
}
case class Phi(cond: Expr, e1: Expr, e2: Expr) extends Expr {
  def children = List(cond, e1, e2)
  def replaceChildren(children: List[Expr]) = { copy(children(0), children(1), children(2)) }
}
object ZeroFloor {
  def apply(e: Expr): Expr = {
    Mux(e > Const(0), e, Const(0))
  }

  def sub(e1: Expr, e2: Expr): Expr = {
    Mux(e2 > e1, Const(0), e1 - e2)
  }
}


//
// Misc.
//
case class NumEntries(e: Expr) extends Expr {
  def children = e::Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
}
case class Size(loType: LoType) extends Expr {
  def children = Nil
  def replaceChildren(children: List[Expr]) = this
}
case class Cast(e: Expr, t: LoType) extends Expr {
  def children = e :: Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
}
case class LowerWord(e: Expr) extends Expr {
  def children = e::Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
}
case class Log2Up(e: Expr) extends Expr {
  def children = e::Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
}


case class FakeUse(e: Expr) extends Expr {
  def children = e::Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
}

/** An expression marked with an annotation to be propagated through the compiler
  *
  *   Any pass that utilizes [[MarkedExpr]]s should define its own mark type, and
  *   then pattern match on `mark` for that type:
  *   {{{
  *     class MyType()
  *     val e = MarkedExpr(e0, new MyType())
  *     // ...
  *     e.mark match {
  *       case m: MyType => // do something ...
  *       case _ =>
  *     }
  *   }}}
  *
  * @param e The expression to be annotated
  * @param mark An annotation of user-defined type
  */
case class MarkedExpr(e: Expr, mark: AnyRef) extends Expr {
  def children = e::Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
}

/** An expression whose value may safely be stored, even if uninitialized
  *
  * This is used to help the interpreter handle programs that are technically
  * correct but which temporarily record an `ENoVal` into a scalar, probably as
  * a result of the [[CommonSubExpressions]] transform, which may move some temporary
  * assignments across [[IfElse]] boundaries. Wrapping in [[Safe]] suppresses errors.
  *
  * @param e The expression to be stored safely.
  */
case class Safe(e: Expr) extends Expr {
  def children = e::Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
}

/** Used in a [[LoInterp]] to execute a _Scala_ function on a dynamic value
  *
  * @param e `LoRes` expression whose dynamic result is an [[EVal]] supplied to function `f`
  * @param from The type of the expresion `e` used as input to `f`
  * @param to The type of the result to be returned by `f`
  * @param f A Scala function to process the result of evaluating `e` into another [[EVal]]
  */
case class Escape(e: Expr, from: LoType, to: LoType, f: EVal => EVal) extends Expr {
  def children = e::Nil
  def replaceChildren(children: List[Expr]) = { copy(children(0)) }
}
