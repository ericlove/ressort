// See LICENSE.txt
/** HiRes: Defines the Ressort Operator Functional Language
  *
  * HiRes is a high-level DSL for expressing sorts, joins, and other algorithms
  * that perform data-dependent data reordering.
  *
  * Used as input to the [[ressort.hi.compiler.HiResCompiler]].
  */
package ressort.hi
import ressort.hi.compiler.OpDag
import ressort.lo


class Line(var string: String, var num: Int=0)


/** A HiRes expression AST annotated with a line-numbered textual representation */
case class ExprListing(
    ast: Expr,
    lines: Seq[Line],
    children: Seq[ExprListing],
    operators: Seq[OperatorListing]=Nil)

/** A HiRes operator AST annotated with a line-numbered textual representation */
case class OperatorListing(
    ast: Operator,
    lines: Seq[Line],
    children: Seq[OperatorListing],
    exprChildren: Seq[ExprListing]=Nil) {

  def string: String = {
    lines.zipWithIndex.map { case (l, i) => l.num = i }
    val strs = lines.map(l => f"${l.num}%4s:  ${l.string}")
    strs.mkString("\n")
  }
}

object OperatorListing {
  /** Standard line length to use when calling `listing` */
  val lineLength = 100
}

/** Expressions: Operations on numbers, keys, and individual records */
sealed abstract class Expr(children_ : Seq[Expr]=Nil, operators_ : Seq[Operator]=Nil) {
  /** All [[Expr]]s contained within this one, in left-to-right order. */
  def children: Seq[Expr] = children_

  /** All [[Operator]]s contained within this [[Expr]], in left-to-right order */
  def operators: Seq[Operator] = operators_

  /** All [[Id]]s used within any level of this expression */
  def ids: Set[Id] = this match {
    case i: Id => Set(i)
    case _ => children.map(_.ids).foldLeft(Set[Id]())(_ ++ _)
  }

  /** Any string representation lines specific to _this_ expression (not its children) */
  def opString: String

  /** Any string representation lines that come _after_ this AST node's children */
  def stringPost: String = ""

  private def makeOp(o: Expr, opFunc: (Expr, Expr) => Expr): Expr = {
    opFunc(this, o) match {
      case Plus(x, Const(0)) => x
      case o => o
    }
  }
    
  def +(o: Expr) = { makeOp(o, (e1, e2) => Plus(e1, e2)) }
  def -(o: Expr) = { makeOp(o, (e1, e2) => Plus(e1, Neg(e2))) }
  def *(o: Expr) = { makeOp(o, (e1, e2) => Mul(e1, e2)) }
  def /(o: Expr) = { makeOp(o, (e1, e2) => Div(e1, e2)) }
  def <(o: Expr) = { makeOp(o, (e1, e2) => Less(e1, e2)) }
  def >(o: Expr) = { makeOp(o, (e1, e2) => Greater(e1, e2)) }
  def <=(o: Expr) = { makeOp(o, (e1, e2) => LessEq(e1, e2)) }
  def >=(o: Expr) = { makeOp(o, (e1, e2) => GreaterEq(e1, e2)) }
  def ===(o: Expr) = { makeOp(o, (e1, e2) => Equal(e1, e2)) }
  def &&(o: Expr) = { makeOp(o, (e1, e2) => And(e1, e2)) }
  def ||(o: Expr) = { makeOp(o, (e1, e2) => Or(e1, e2)) }

  def toLoFloat: Expr = Cast(this, Payload(lo.LoFloat()))
  def toLoDouble: Expr = Cast(this, Payload(lo.LoDouble()))
  def toLoInt: Expr = Cast(this, Payload(lo.LoInt()))

  def addToLine(line: Line): ExprListing = {
    val childListings = children.length match {
      case 0 => line.string += s"$opString$stringPost"; Nil
      case 1 => {
        line.string += s"$opString("
        val c = children.head.addToLine(line)
        line.string += s")$stringPost"
        Seq(c)
      }
      case 2 => {
        val c0 = children(0).addToLine(line)
        line.string += s" $opString "
        val c1 = children(1).addToLine(line)
        line.string += stringPost
        Seq(c0, c1)
      }
      case _ => {
        line.string += s"$opString("
        val cHead = children.head.addToLine(line)
        val cTail = for (c <- children.tail) yield {
          line.string += s", "
          c.addToLine(line)
        }
        cHead +: cTail
      }
    }
    ExprListing(this, Seq(line), childListings)
  }

  def listing(indent: Int, maxLine: Int): ExprListing = {
    val spaces = "  "*indent
    val singleLine = {
      val line = new Line(spaces)
      addToLine(line)
    }
    lazy val childListings = children.map(_.listing(indent+1, maxLine))
    if (singleLine.lines.head.string.length < maxLine) {
      val line = new Line(spaces)
      addToLine(line)
    } else if (children.length == 2) { 
      val header = new Line(s"$spaces(")
      val cleft = childListings(0)
      val cright = childListings(1)
      val middle = new Line(s"$spaces)  $opString  (")
      val footer = new Line(s"$spaces)")
      val lines = Seq(header) ++ cleft.lines ++ Seq(middle) ++ cright.lines ++ Seq(footer)
      ExprListing(this, lines, Seq(cleft, cright))
    } else {
      val clistings = childListings
      val clines = clistings.map(_.lines).flatten
      val header = new Line(s"$spaces$opString (")
      val footer = new Line(s"$spaces)")
      ExprListing(this, header +: clines :+ footer, clistings)
    }
  }

}

sealed abstract class CommutativeOp(val symbol: String)

case object PlusOp extends CommutativeOp("+")
case object MulOp extends CommutativeOp("*")
case object MinOp extends CommutativeOp("min")
case object MaxOp extends CommutativeOp("max")
case object AndOp extends CommutativeOp("&&")
case object OrOp extends CommutativeOp("||")

sealed abstract class CommutativeOpExpr(op: CommutativeOp, infix: Boolean=true) extends Expr {
  def e1: Expr
  def e2: Expr
  override def children = e1 :: e2 :: Nil

  def opString = (op.symbol)
}

object CommutativeOpExpr {
  def apply(op: CommutativeOp, e1: Expr, e2: Expr): CommutativeOpExpr = op match {
    case PlusOp => Plus(e1, e2)
    case MulOp => Mul(e1, e2)
    case AndOp => And(e1, e2)
    case OrOp => Or(e1, e2)
    case MinOp => ???
    case MaxOp => ???
  }
}

case class Plus(e1: Expr, e2: Expr) extends CommutativeOpExpr(PlusOp) {
  override def toString = e2 match {
    case Neg(e) => s"($e1 - $e)"
    case _ => s"($e1 + $e2)"
  }
}

case class Div(e1: Expr, e2: Expr) extends Expr(e1::e2::Nil) {
  override def toString = s"($e1 / $e2)"

  def opString = "/"
}
case class Mul(e1: Expr, e2: Expr) extends CommutativeOpExpr(MulOp) {
  override def toString = {
    def addParens(e: Expr): String = e match {
      case Const(n) => s"$n"
      case m: Mul => s"$m"
      case other => s"($other)"
    }
    addParens(e1) + " * " + addParens(e2)
  }
}
case class Neg(e: Expr) extends Expr(e::Nil) {
  override def toString = s"-($e)"

  def opString = "-"
}
case class Pow(base: Expr, exp: Expr) extends Expr(base::exp::Nil) {
  def opString = ("^")
}
case class Pow2(base: Expr) extends Expr(base::Nil) {
  def opString = ("Pow2")
}
case class Log2Up(e: Expr) extends Expr(e::Nil) {
  def opString = ("Log2Up")
}
case class Const(n: Int) extends Expr() {
  override def toString = s"$n"

  def opString = (s"$n.I")
}
case class FloatConst(f: Float) extends Expr() {
  def opString = (s"$f.f")
}
case class DoubleConst(d: Double) extends Expr() {
  def opString = (s"$d.d")
}
case class Less(e1: Expr, e2: Expr) extends Expr(e1::e2::Nil) { def opString = ("<") }
case class Greater(e1: Expr, e2: Expr) extends Expr(e1::e2::Nil) { def opString = (">") }
case class LessEq(e1: Expr, e2: Expr) extends Expr(e1::e2::Nil) { def opString = ("<=") }
case class GreaterEq(e1: Expr, e2: Expr) extends Expr(e1::e2::Nil) { def opString = (">=") }
case class Equal(e1: Expr, e2: Expr) extends Expr(e1::e2::Nil) { def opString = ("==") }
case class Id(name: String) extends Expr {
  def :=(o: Operator) = Assign(this, o)

  def opString = (name)

  override def addToLine(line: Line): ExprListing = {
    line.string += name
    ExprListing(this, Seq(line), Seq())
  }
}
case class UField(field: Int) extends Expr(Nil) {
  def opString = ""
  override def stringPost =(s"<$field>")
}

case class BitRange(e: Expr, msb: Expr, lsb: Expr) extends Expr(e::msb::lsb::Nil) {
  def opString = ("BitRange")
}
case class Length(o: Operator) extends Expr(operators_ = o :: Nil) { def opString = ("Length") }
case object True extends Expr() { def opString = ("True") }
case object False extends Expr() { def opString = ("False") }
case class And(e1: Expr, e2: Expr) extends CommutativeOpExpr(AndOp)
case class Or(e1: Expr, e2: Expr) extends CommutativeOpExpr(OrOp)
case class Not(e: Expr) extends Expr(e::Nil) { def opString = ("!") }
case class Cast(e: Expr, t: Payload) extends Expr(e::Nil) {
  def opString = ("Cast")
  override def stringPost =(s"< $t >")
}

/** AST for an array operation in HiRes
  *
  * @param children All [[Operator]]s contained within this one, in syntactic 
  *                 order (left to right inside operator constructor).
  *
  * @param exps All [[Expr]]s contained within this [[Operator]], in syntactic
  *             order (left to right inside the constructor).
  */
sealed abstract class Operator(
    val name: String,
    val children: Seq[Operator]=Nil,
    val exprs: Seq[Expr]=Nil,
    val exprNames: Seq[String]=Nil) {
  /** Returns a string representation of this [[Operator]] with any children
    * replaced by `childLength`-character abbreviations.
    */
  def abbreviated(childLength: Int): String = {
    s"$name(" +
      children.foldLeft("") { case (s,c) => s"$s, ${c.toString.take(childLength)}" } +
      ")"
  }

  def apply(e: Expr): Eval = {
    Eval(this, e)
  }

  def fields(ids: Id*): Operator = zip(ids.map(i => i -> i):_*)

  def projFields(ids: Id*): Operator = project(ids.map(i => i -> i):_*)

  def zip(es: (Id, Expr)*) = {
    Let(es.map(p => p._1 := this(p._2)), in = Zip(es.map(p => IdOp(p._1)):_*))
  }

  def project(es: (Id, Expr)*): Operator = {
    Let(es.map(p => p._1 := this(p._2)), in = Project(es.map(p => IdOp(p._1)):_*))
  }

  def projectWithPosition(position: Id='position): Operator = {
    Let(
      List(
        position := Position(this)),
      in = Project(this, IdOp(position)))
  }

  def zipWithPosition(position: Id='position): Operator = {
    Let(
      List(
        position := Position(this)),
      in = Zip(this, IdOp(position)))
  }

  def cast(t: Payload): Eval = this(Cast(UField(0), t))

  def opString: String = name

  def addExprsToLine(line: Line): Seq[ExprListing] = {
    for (((e, n), i) <- exprs.zip(exprNames).zipWithIndex) yield {
      if (i > 0)
        line.string += s", $n="
      else
        line.string += s"[$n="
      val res = e.addToLine(line)
      if (i == exprs.length-1)
        line.string += "]"
      res
    }
  }

  def exprListing(indent: Int, maxLine: Int): Seq[ExprListing] = {
    val spaces = "  "*indent
    val elistings = exprs.map(_.listing(0, maxLine - spaces.length))
    elistings.zip(exprNames).map { case (e,n) =>
      e.lines.head.string = s"$n = " + e.lines.head.string
    }
    elistings.map(_.lines.map(l => l.string = spaces + "  " + l.string))
    elistings.dropRight(1).map(_.lines.last.string += ",")
    elistings
  }


  def addToLine(line: Line): OperatorListing = {
    line.string += s"$opString"
    val elistings = addExprsToLine(line)
    val childListings = for ((c, i) <- children.zipWithIndex) yield {
      if (i == 0) line.string += "("
      if (i > 0) line.string += ", "
      c.addToLine(line)
    }
    if (children.nonEmpty)
      line.string += ")"
    OperatorListing(
      this,
      lines = Seq(line),
      children = childListings,
      exprChildren = elistings)
  }


  def listing(indent: Int, maxLine: Int): OperatorListing = {
    val spaces = "  "*indent
    val singleLine = addToLine(new Line(spaces))
    val singleExprStr = {
      if (exprs.nonEmpty) {
        val res = addExprsToLine(new Line(""))
        res.head.lines.head.string
      } else {
        ""
      }
    }
    if (singleLine.lines.head.string.length < maxLine) {
      val line = new Line(spaces)
      addToLine(line)
    } else {
      val clistings = children.map(_.listing(indent + 1, maxLine))
      val clines = clistings.map(_.lines).flatten
      clistings.dropRight(1).map(_.lines.last.string += ", ")
      var elistings = Seq[ExprListing]()
      val header = {
        val line = new Line(s"$spaces$opString")
        if (singleExprStr.length + line.string.length < maxLine) {
          if (exprs.nonEmpty) {
            elistings = addExprsToLine(line)
          }
          line.string += " ("
          Seq(line)
        } else  {
          line.string += " ["
          elistings = exprListing(indent + 1, maxLine)
          val elines = elistings.map(_.lines).flatten
          Seq(line) ++ elines ++ Seq(new Line(spaces +"  ] ("))
        }
      }
      val footer = new Line(s"$spaces)")
      OperatorListing(this, header ++ clines :+ footer, clistings, elistings)
    }
  }
}

object Operator {
  private var numIds = 0

  def newId(): Id = { numIds += 1; Id(s"t_$numIds") }
}

/** Base case: an `Operator` that is just an array input */
case class IdOp(id: Id) extends Operator("IdOp", exprs=Seq(id), exprNames=Seq("id")) {
  override def opString = (id.name)

  override def addToLine(line: Line): OperatorListing = {
    val child = id.addToLine(line)
    OperatorListing(this, Seq(line), Nil, Seq(child))
  }
}

/** Causes the value `o` to be assigned to `id`, and returns the value of `o` */
case class Assign(id: Id, o: Operator) extends Operator("Assign", o::Nil) {
  override def opString = (s"${id.name} := ")
}

case class Let(assigns: Seq[Assign], in: Operator) extends Operator("Let", assigns :+ in)


/** Used by [[ressort.hi.compiler]] at various stages to represent
  * an operator whose inputs are stages in an [[ressort.hi.compiler.OpDag]]
  *
  * @param id Is the _node id_ of the [[HiDag]] or [[LoDag]] for which this stands.
  */
case class DagOp(id: Option[Integer]=None) extends Operator(s"DagOp_$id")

case class Cat(head: Operator, tail: Operator*) extends Operator("Cat", head +: tail)

case class Uncat(o: Operator, n: Int) extends Operator("Uncat", o::Nil) {
  override def abbreviated(childLength: Int): String = {
    s"Uncat(${o.toString.take(childLength)}, $n)"
  }
}

case class Project(ops: Operator*) extends Operator("Project", ops) { assert(ops.length > 0) }

case class Zip(ops: Operator*) extends Operator("Zip", ops)

sealed abstract class Sort(name_ : String, o_ : Operator) extends Operator(name_, o_ ::Nil)

case class InsertionSort(o: Operator, keys: List[FieldName]=Nil) extends Sort("InsertionSort", o) {
  override def opString = s"InsertionSort[$keys]"
  assert(keys.nonEmpty)
}

case class MergeSort(o: Operator) extends Sort("MergeSort", o)

case class Cross(left: Operator, right: Operator) extends Operator("Cross", left::right::Nil)

case class HashJoin(
    left: Operator,
    right: Operator,
    hash: Operator,
    test: Option[Expr]=None,
    parallel: Boolean=false)
  extends Operator("HashJoin", left::right::hash::Nil, test.toList, List("test"))


case class Histogram(
    keys: Operator,
    slices: Expr,
    padding: Expr=Const(0))
  extends Operator("Histogram", keys::Nil, slices::padding::Nil, List("slices", "padding"))


/** Move records to their designated partitions using `hist` as a
  * the per-partition histogram.
  *
  * @param parallel Indicates that `hist` is a parallel histogram, but
  *              has been merged with [[Offsets]] to output
  *              a single partitioned array
  */
case class Partition(
    keys:     Operator,
    values:   Operator,
    hist:     Operator,
    parallel: Boolean = false,
    disjoint: Boolean = false)
  extends Operator("Partition", keys::values::hist::Nil)

case class Flatten(o: Operator) extends Operator("Flatten", o::Nil)

/** Takes only the elements of the last sub-array of `o` */
case class LastArray(o: Operator) extends Operator("LastArray", o::Nil)

/** Prefix-sums the number of valid elements in each sub-array to yield its offset
  * 
  * The input `o` can either be a `Hist` type, (marked with `inPlace`), in which case
  * its [[Index]]-valued elements are summed in place, or an arbitrary `Arr(..)` type,
  * in which case the number of valid elements in each element are summed to produce a
  * newly-allocated histogram in the output.
  * Histograms created in parallel can be aggregated by setting `depth` to the degree
  * nesting from "threads" in the input (see `depth`'s own description for detail).
  *
  * @param o      Input for which to generate sub-array offsets
  * @param depth The number of innermost levels to merge as part of the same
  *               logical histogram. Thus, if a single split operator created `N`
  *               parallel histogram copies, `depth=1` would combine the `i`th
  *               partitions of each histogram into one contiguous extent before
  *               the combined `i+1`th partitions from each thread, and so on.
  * @param inPlace If set, this will cause the array's inner elements themselves 
  *                 (which must be of type [[Index]]) to be reduced in-place, rather
  *                 than each array's vector length, and no new buffer will be allocated.
  *                 If the input is a [[Hist]] type, this will be set automatically.
  * @param disjoint If set, this causes the reduction to be reset between arrays at
  *                 the specified `depth`, as they reside in separate buffers.
  */
case class Offsets(
    o:  Operator,
    depth: Int=0,
    inPlace: Boolean=false,
    disjoint: Boolean=false)
  extends Operator("Offsets", o::Nil)

/** Restores each entry of a histogram-partitioned array to contain
  * its partition's starting offset in the buckets array and completes
  * partitioning by adding a nesting layer.
  *
  * The array's internal histogram must be in the "moved" state.  This transitions it
  * to the "restored" state and completes the addition of a nesting layer.
  */
case class RestoreHistogram(
    values: Operator,
    hist:   Operator,
    parallel:  Boolean = false)
  extends Operator("RestoreHistogram", values::hist::Nil)


/** Builds and returns a hash table with variable-length sub-arrays.
  *
  * @param o The records to be hashed. Their structure should be exactly that of the desired table.
  * @param aggregates Fields that should be aggregated, along with their respective operators. Any field
  *                   that does _not_ appear in `aggregates` must match exactly, or a new entry is created.
  * @param hash An optional specification of each input record's bucket. This should be aligned with `o`.
  *             If none is specified, a function will be chosen based on the input type and number of buckets.
  * @param buckets An optional number of buckets in the table. If empty, one will be set based on
  *                the width of the keys (non-aggregate fields) or `hash` if specified.
  * @param slots An optional number of entries per hash bucket. By default, one will be chosen based on
  *              the input types to ensure at least one cache line per bucket.
  * @param inlineCounter If set, an extra record will be pre-pended to each bucket, and
  *                       its first field will be used as a counter of the number of
  *                       filled slots in the first chunk, until it is full, at which
  *                       point separate counter and pointer arrays will be allocated.
  */
case class HashTable(
    o: Operator,
    aggregates: List[(FieldName, CommutativeOp)] = Nil,
    hash: Option[Operator] = None,
    buckets: Option[Expr] = None,
    slots: Option[Expr] = None,
    inlineCounter: Boolean = false)
  extends Operator(
      "HashTable",
      List(Some(o), hash).flatten,
      buckets.toList ++ slots.toList,
      List("buckets", "slots"))

sealed trait FieldName
case class UFieldName(i: Int) extends FieldName
case class NFieldName(i: Id) extends FieldName


case class Eval(o: Operator, func: Expr) extends Operator("Eval", o::Nil, func::Nil) {
  override def abbreviated(childLength: Int): String = {
    s"Eval(${o.toString.take(childLength)} : $func)"
  }

  override def addToLine(line: Line): OperatorListing = {
    line.string += s"Eval ("
    val ochild = o.addToLine(line)
    line.string += s") { "
    val echild = func.addToLine(line)
    line.string += " }"
    OperatorListing(
      this,
      Seq(line),
      Seq(ochild),
      Seq(echild))
  }

  override def listing(indent: Int, maxLine: Int): OperatorListing = {
    val oListing = o.listing(0, maxLine)
    val eListing = func.listing(0, maxLine)
    val singleLineChildren = (oListing.lines.length == 1) && (eListing.lines.length == 1)
    val headlines = Seq(oListing.lines.head, eListing.lines.head)
    val spaces = "  "*indent
    val overhead = s"${spaces}Eval () {}".length
    if (singleLineChildren && headlines.map(_.string.length).sum < maxLine - overhead) {
      val line = new Line(spaces)
      addToLine(line)
    } else {
      val oListing = o.listing(indent + 3, maxLine)
      val eListing = func.listing(indent + 1, maxLine)
      val header = new Line(s"${spaces}Eval (")
      val closeOp = new Line(s"$spaces) {")
      val footer = new Line(s"$spaces}")
      val lines = Seq(header) ++ oListing.lines ++ Seq(closeOp) ++ eListing.lines ++ Seq(footer)
      OperatorListing(this, lines, Seq(oListing), Seq(eListing))
    }
  }
}

sealed abstract class Reduction(
    name_ : String,
    val o_ : Operator,
    val op_ : CommutativeOp,
    val init_ : Option[Expr]=None)
  extends Operator(name_, o_ :: Nil) {
  
  override def abbreviated(childLength: Int): String = {
    val initStr = init_.map(i => s", $i").getOrElse("")
    s"${name_}(${o_.toString.take(childLength)}, ${op_}$initStr)"
  }

  override def opString = s"$name[${op_.symbol}]"

  override def addToLine(line: Line): OperatorListing = {
    line.string += s"$opString("
    val clisting = o_.addToLine(line)
    val elisting = init_.map { i => line.string += ", "; i.addToLine(line) }
    line.string += ")"
    OperatorListing(this, Seq(line), Seq(clisting), elisting.toSeq)
  }
}

case class Reduce(
    o: Operator,
    op: CommutativeOp,
    init: Option[Expr]=None)
  extends Reduction("Reduce", o, op, init)

case class NestedReduce(
    o: Operator,
    op: CommutativeOp,
    init: Option[Expr]=None)
  extends Reduction("NestedReduce", o, op, init)


/** An [[Operator]] that splits its input array into `slices` equal-sized
  * slices.
  *
  * @param o_ The operator producing the input array to this `Split()` operation
  *
  * @note that once slice may have a different size in the case that the input
  *       size is not a perfect parallelple of `slices`.
  */
sealed trait Split { this: Operator =>

  /** The number of equal-sized pieces into which to divide the input */
  val slices: Expr

  /** The number of empty elements to insert between each slice
    *
    * @note since this is an in-place operator, the effect of padding will not
    *       manifest until a non-in-place operation is applied to this result,
    *       causing a new deep buffer array to be allocated.
    */
  val padding: Expr

  /** True iff the elements of this array are stored in physically disjoint buffers */
  val disjoint: Boolean

  override def abbreviated(childLength: Int): String = {
    val start = s"${name}(${this.toString.take(childLength)}, $slices"
    val middle = if (padding != Const(0)) ", $padding" else ""
    start + middle + ")"
  }

}

/** A [[Split]] operator that allows subsequent operations on each of its
  * sub-arrays to execute in ''parallel''.
  */
case class SplitPar(
    o: Operator,
    slices: Expr,
    padding: Expr = Const(0),
    disjoint: Boolean = false)
  extends Operator("SplitPar", o::Nil, Seq(slices, padding), Seq("slices", "pad")) with Split

/** A [[Split]] operator that requires subsequent operations on ech of its
  * sub-arrays to execute ''sequentially''
  */
case class SplitSeq(
    o: Operator,
    slices: Expr,
    padding: Expr = Const(0),
    disjoint: Boolean = false)
  extends Operator("SplitSeq", o::Nil, Seq(slices, padding), Seq("slices", "pad")) with Split

case class Compact(
    o: Operator,
    padding: Expr=Const(0),
    hist: Option[Operator]=None)
  extends Operator(
    "Compact",
    List(Some(o), hist).flatten,
    Seq(padding),
    Seq("pad")
  ) {
  
}

case class Position(o: Operator) extends Operator("Position", o::Nil)

case class Mask(
    o: Operator,
    cond: Operator)
  extends Operator("Mask", o::cond::Nil)

case class Collect(
    o: Operator)
  extends Operator("Collect", o::Nil)

case class Gather(
    indices: Operator,
    target: Operator)
  extends Operator("Gather", indices::target::Nil)

case class Block(o: Operator, nest: Boolean=false, nonFusable: Boolean=false) extends Operator((if (nonFusable) "BlockAll" else "Block"), o::Nil)

case class Hash64(o: Operator, bits: Int) extends Operator("Hash64", o::Nil)
