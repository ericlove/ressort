// See LICENSE.txt
package ressort.lo.interp
import scala.collection.immutable.ListMap
import scala.collection.mutable.HashMap
import scala.collection.mutable.HashSet
import scala.collection.mutable.ArrayBuffer
import ressort.lo._

case class InterpError(message: String, lines: Option[LoAstLines], uninitialized: Boolean=false) extends Throwable {
  override def getMessage(): String = lines match {
    case Some(l) => s"On lines ${l.start} -- ${l.end}:\n" +message
    case None => message
  }
}



class LoInterp(val parent: Option[LoInterp] = None) {

  protected val values = new HashMap[ScopedSym, EAddr]()

  private def setValue(s: ScopedSym, v: EVal): EAddr = {
    val addr = if (values.contains(s)) {
      values(s)
    } else {
      val addr = new EAddr()
      values(s) = addr
      addr
    }
    addr.value = v
    addr
  }

  /** Stores the result of each executed [[Printf]] */
  private val console = ArrayBuffer[String]()

  def consoleLog(): String = console.mkString("\n")

  val tempIds = new TempIds("_ectx_")

  override def toString() = {
   dumpLines().foldLeft("") { _+_ }
  }

  /** Returns all the ScopedSyms that are within scope in `scope` */
  def findReachable(scope: Symtab): Seq[ScopedSym] = {
    val scopeds = scope.myScope map { item => ScopedSym(item, scope) }
    scope.parent match {
      case None => scopeds
      case Some(p) => scopeds ++ findReachable(p)
    }
  }

  /** Evaluates a typed AST node, updating state, and returns any return value or throws an exception */
  def eval(ast: TypedLoAst): Option[EVal] = {
//    try {
      def clearAddrs(ast: TypedLoAst): Unit = {
        ast.exprChildren.map(_.eaddr = None)
        ast.children.map(clearAddrs)
      }
      clearAddrs(ast)
      evalInner(ast)
//    } catch {
//      case err: InterpError =>
//        val listing = ast.lines.map(_.listing.toString).getOrElse("")
//        val errLines = err.lines.map(l => s"On lines ${l.start} -- ${l.end}:\n").getOrElse("\n")
//        throw new AssertionError(s"Execution error:\n$listing\n$errLines${err.message}\n")
//    }
  }

  def valueOf(expr: Expr, scope: Symtab): EVal = {
    addrOf(scope(expr)).value
  }

  /** Evaluates a typed expression in this context, and returns the result or throws an exception */
  def eval(expr: TypedExpr): EVal = evalInner(expr)

  /** Returns a string representation of this `EContext`'s contents */
  def dumpLines(
      childLines: Seq[String]=Seq(),
      markedSet: Set[EAddr]=Set()): Seq[String] = {
    val div = Seq("-"*80+"\n")
    val markedHashSet = HashSet[EAddr]() ++ markedSet
    val myLineSets = values map { p =>
        try {
          val addr = p._2
          val sym = p._1
          val obj = addr.value
          val itemLines = {
            if(markedHashSet.contains(addr))
              Seq[String]()
            else {
              markedHashSet += addr
              addr.value.dumpLines(Seq[String](), markedHashSet)(Some(this))
            }
          }
          val indentedItemLines: Seq[String] = itemLines map { l => "    "+l }
          div ++ Seq(sym + "    -->    ["+ obj.toString + "]\n") ++ indentedItemLines
        } catch {
          case ae: AssertionError => Seq(ae.toString)
        }
    }
    val myLines = myLineSets.foldLeft(Seq[String]()) { _ ++ _ }
    val indentedChildLines: Seq[String] = childLines map { line => "    "+line }
    val allLines: Seq[String] = indentedChildLines ++ myLines
    allLines
  }


  def apply(scoped: ScopedSym): EVal = {
    if(values.contains(scoped))
      values(scoped).value
    else {
      parent match {
        case Some(p) => p(scoped)
        case None => ENoVal
      }
    }
  }


  private def refOfId(scoped: ScopedSym, lines: Option[LoAstLines], dumpEnv: Boolean=false): EAddr = {
    if(values.contains(scoped))
      values(scoped)
    else {
      parent match {
        case Some(p) => { p.refOfId(scoped, lines, dumpEnv) }
        case None => {
          val epilogue = {
            if(dumpEnv)
              " not in " + this.toString
            else
              "-> [NULL]     !!!!!!!!!!"
          }
          throw InterpError("Id " + scoped + epilogue, lines)
        }
      }
    }
  }

  private def addrOf(lval: TypedExpr): EAddr = {
    def helper(lval: TypedExpr): EAddr = {
      lval.eaddr.map(return _)
      def cache(addr: EAddr): EAddr = {
        // Make sure the LValue is only constants or symbols; otherwise, can't cache
        // (E.g. if it were `arr[n]` then its address would be different for each value of `n`)
        def valid(l: LValue): Boolean = l match {
          case s: SymLike => true
          case Field(l2, _) if valid(l2) => true
          case UField(l2, _, _) if valid (l2) => true
          case _ => false
        }
        if (valid(lval.expr.toLValue))
          lval.eaddr = Some(addr)
        addr
      }
      lval.expr.toLValue match {
        case s: SymLike if lval.scopedSym.nonEmpty => cache(refOfId(lval.scopedSym.get, lval.lines))
        case s: SymLike => refOfId(lval.scope.unique(s), lval.lines)
        case Deref(_) => helper(lval.children.head).value.toEPtr(lval.lines).ref
        case Subsc(_, n) => {
          val addr = helper(lval.children.head)
          val index = evalNum(lval.children(1)).toEInt(lval.lines).i.toInt
          addr.value match {
            case EArray(items, len) => {
              val arr = addr.value.toEArray(lval.lines)
              if (index >= arr.len || index < 0) {
                throw InterpError(s"Array index $index out of bounds (${arr.len}) in ${lval.expr}", lval.lines)
              }
              arr.a(index)
            }
            case other => throw InterpError(s"Non-array value $other used where array expected\n" + dumpLines().mkString("\n"), lval.lines)
          }

        }
        case Field(_, name) => {
          val addr = helper(lval.children.head)
          val struct = addr.value.toEStruct(lval.lines)
          for (f <- struct.fields) {
            if (f._1 == name)
              return cache(f._2)
          }
          ???
        }
        case UField(_, n, id) => {
          val addr = helper(lval.children.head)
          val fields = addr.value match {
            case s: EStruct => s.fields.map(_._2)
            case r: ERecord => r.fields
            case _ => throw new InterpError(s"${addr.value} used where struct or record required", lval.lines)
          }
          cache(fields(n))
        }
      }
    }
    helper(lval)
  }

  private def evalInner(e: TypedExpr): EVal = e.expr match {
    case Mux(cond, e1, e2) => {
      val select: Boolean = evalBool(e.children.head).toEBool(e.lines).b
      if(select)
        evalInner(e.children(1))
      else
        evalInner(e.children(2))
    }
    case _ => try {
      e.loType match {
        case iv: IntValued => evalNum(e)
        case f: LoFloat => evalNum(e)
        case d: LoDouble => evalNum(e)
        case Bool(_) => evalBool(e)
        case Ptr(_, _) => evalPtr(e)
        case NullType => EPtr(ENull)
        case r: Record => evalRecord(e)
        case other => {
          val err = "LoResInterp can't yet evaluate expressions of type \n\t\t"+other+"\n"
          throw InterpError(err, e.lines)
        }
      }
    } catch {
//      case err: AssertionError => {
//        throw InterpError(
//          "\n\nInterpreter Eval Error:\n\t" +
//          err+"\nCan't evaluate type "+e.loType+" of\n\t\t"+e.expr+"\nin:\n"+this+
//          "\n\n")
//      }
      case err: AssertionError => throw(err)
    }
  }

  /** Allocates a variable of type `t` and returns it */
  private def initLo(t: LoType, lines: Option[LoAstLines]): EVal =  {
    val value = t match {
      case Struct(name, fields, const) => {
        val fieldAddrs = fields map { case (f,t) => (f -> initLo(t, lines)) }
        EStruct(fieldAddrs.map(p => p._1 -> new EAddr(p._2)))
      }
      case r: Record => {
        val fieldAddrs = r.fields.toIndexedSeq.map(_.loType).map(initLo(_, lines))
        ERecord(fieldAddrs.map(new EAddr(_)))
      }
      case p: Primitive => ENoVal
      case _ => {
        throw InterpError("Cannot allocate object of type "+t, lines)
      }
    }
    value
  }




  /** Allocates an object of the given type expression and returns it */
  private def initObj(loType: LoType, scope: Symtab, lines: Option[LoAstLines], length: Option[TypedExpr]): EVal = {
    // For first layer of the Dec's type, we allocate arrays as needed;
    // for any expanded TypeRef, we allocate directly from the corresponding
    // LoType, which must not contain an array.
    loType match {
      case Arr(t2, _) if length.nonEmpty => {
        val len = evalNum(length.get).toEInt(lines).i.toInt
        val elemArray = Array.fill[EAddr](len)(new EAddr(initObj(t2, scope = scope, lines = lines, length = None)))
        val arr = EArray(elemArray, len)
        arr
      }
      case TypeRef(v, _) => scope(v, lines).loType match {
        case Struct(name, fields, const) => initLo(Struct(name, fields, const), lines)
        case _ => {
          throw InterpError("Can't have a TypeRef to a non-Struct!", lines)
        }
      }
      case s: Scalar => initLo(s, lines)
      case _ => {
        throw InterpError("Type expression "+ loType +" cannot be initialized.", lines)
      }
    }
  }

  /** Converts the RHS of an assignment to the defined type of its LValue
    *
    * For numerical assignments, the RHS may have a different width or signedness from
    * the target variable.  If so, the resulting [[EVal]] must be coerced.
    */
  private def implicitCast(rhs: EVal, lhs: LoType): EVal = {
    lhs match {
      case i: IntValued => {
        val rhInt = rhs.toEInt(None)
        EInt(rhInt.i, widthBytes=i.maxBytes, signed=i.signed)
      }
      case f: LoFloat => rhs.toEFloat(None)
      case d: LoDouble => rhs.toEDouble(None)
      case _ => rhs
    }
  }

  /** Returns the result of an explicit [[Cast]] expression on value `eval` */
  private def cast(eval: EVal, to: LoType): EVal = {
    (eval, to) match {
      case (i: EInt, iv: IntValued) => EInt(i.i, widthBytes=iv.minBytes, signed=iv.signed)
      case (i: EInt, d: LoDouble) => EDouble(i.toBigInt.toDouble)
      case (i: EInt, f: LoFloat) => EFloat(i.toBigInt.toFloat)
      case (d: EDouble, iv: IntValued) => EInt(d.d.toLong, widthBytes=iv.minBytes, signed=iv.signed)
      case (d: EDouble, ld: LoDouble) => d
      case (d: EDouble, lf: LoFloat) => EFloat(d.d.toFloat)
      case (f: EFloat, iv: IntValued) => EInt(f.f.toLong, widthBytes=iv.minBytes, signed=iv.signed)
      case (f: EFloat, ld: LoDouble) => EDouble(f.f.toDouble)
      case (f: EFloat, lf: LoFloat) => f
      case _ => ???
    }
  }

  /** Evaluates a typed AST node, updating state, and returns any return value
    *
    * This is the internal dispatch for each different AST type.
    * All internal type-specific AST node handlers should call this, while external users call `eval`, which
    * catches any internal error exceptions and generates an appropriate message tied to a single listing.
    */
  private def evalInner(o: TypedLoAst): Option[EVal] = {
    o.ast match {
      case d @ Dec(_, _) => {
        val sym = o.scope.unique(d.v)
        val obj = initObj(d.loType, o.scope, o.lines, None)
        setValue(sym, obj)
        None
      }
      case ha @ HeapAlloc(_, _) => {
        val length = ha.length.map(_ => o.exprChildren(1))
        val loType = o.exprChildren.head.loType match {
          case Ptr(t, _) => t
          case _ => ???
        }
        val obj = initObj(loType, o.scope, o.lines, length)
        val lvAddr = addrOf(o.exprChildren.head)
        lvAddr.value = EPtr(new EAddr(obj))
        None
      }
      case f @ Free(lv) => {
        addrOf(o.exprChildren.head).value = ENoVal
        None
      }
      case a @ Assign(lval, e) => {
        val texpr = o.exprChildren(1)
        val addr = addrOf(o.exprChildren.head)
        val lvType = o.exprChildren.head.loType
        addr.value = try {
          implicitCast(evalInner(texpr), lvType)
        } catch {
          case ie: InterpError if ie.uninitialized => e match {
            case Safe(e1) => ENoVal
            case _ => throw ie
          }
        }
        None
      }
      case da @ DecAssign(_, _, _) => {
        val sym = o.scope.unique(da.sym)
        val loType = o.scope(da.sym).loType
        val value = evalInner(o.exprChildren.head)
        setValue(sym, implicitCast(value, loType))
        None
      }
      case p: Prefetch => None
      case ar: AssignReturn => {
        val addr = addrOf(o.exprChildren.head)
        val appRes = evalApp(o, ar.a, isAssignReturn=true)
        val newEVal: EVal = appRes match {
          case Some(eval) => eval
          case None => {
            // should be unreachable after type checking
            throw InterpError("Void return Some(v)alue in "+ar, o.lines)
          }
        }
        addr.value = newEVal
        None
      }
      case fd: FuncDec => {
        val sym = o.scope.unique(fd.name)
        val typedBody = o.children(0)
        val params = fd.params //map { case (p,texpr) => p -> o.scope(texpr) }
        setValue(sym, EFunc(params, typedBody))
        None
      }
      case a @ App(_, _) => evalApp(o, a)
      case b @ Block(ops) => {
        for (op <- o.children) {
          val res = evalInner(op)
          res.map(v => return Some(v))
        }
        None
      }
      case fs: ForSeq => evalLoop(o, fs.index, fs.min, fs.max, fs.stride, fs.body)
      case fp: ForPar => evalLoop(o, fp.index, fp.min, fp.max, fp.stride, fp.body)
      case w @ While(cond, body) => evalWhile(o, w)
      case ie @ IfElse(cond, ifBody, elseBody) => evalIfElse(o, ie)
      case td @ Typedef(struct) => None
      case ret @ Return(expr) => Some(evalInner(o.exprChildren.head))
      case pf: Printf => {
        val evals = o.exprChildren.map(evalInner)
        val vals = evals map {
          _ match {
            case EInt(i, _, _) => i
            case EBits(b) => b
            case EFloat(f) => f
            case EDouble(d) => d
            case EBool(b) => b
            case other => throw InterpError(s"Don't know how to print value of type $other", o.lines)
          }
        }
        val str = pf.fmt.format(vals.toList:_*)
        console += str
        println(str)
        None
      }
      case Nop => None
      case ps @ PrefixSum(e, range) => evalPrefixSum(o, ps)
      case RotRight(arr, shamt, range) => evalRotate(o, arr, shamt, range, left=false)
      case RotLeft(arr, shamt, range) => evalRotate(o, arr, shamt, range, left=true)
      case rv @ Reverse(arr, range) => evalReverse(o, rv)
      case ms @ Memset(arr, value, range) => evalMemset(o, ms)
      case _ => {
        val err = "Statement type '"+o.ast+"' not yet implemented in interpreter"
        throw InterpError(err, o.lines)
      }
    }
  }


  def evalApp(o: TypedLoAst, a: App, isAssignReturn: Boolean=false) = {
    val scope = o.scope
    val noFuncError = "Function "+a.func+" does not exist in current scope."
    val funcArgMap: Map[SymLike, EVal] =
      Map(a.args map { case (name, arg) => (name, evalInner(scope(arg, o.lines))) }: _*)
    val func = values(scope.unique(a.func)).value.toEFunc(o.lines)
    val cscope = func.body.scope
    val typedArgs = if (isAssignReturn) o.children.head.exprChildren else o.exprChildren
    for (((name, arg), typed) <- a.args.zip(typedArgs)) {
      val value = evalInner(typed)
      val scoped = cscope.unique(name)
      setValue(scoped, value)
    }
    val res = evalInner(func.body)
    res
  }

  def evalIfElse(o: TypedLoAst, ie: IfElse) = {
    val typedCond = o.scope(ie.cond, o.lines)
    val typedIfBody = o.children(0)
    val typedElseBody = o.children(1)

    if(evalBool(typedCond).b) {
      evalInner(typedIfBody)
    } else {
      evalInner(typedElseBody)
    }
  }

  def evalLoop(
      o: TypedLoAst,
      index:  SymLike,
      min:    Expr,
      max:    Expr,
      stride: Expr,
      body: LoAst): Option[EVal] = {
    val childScope = o.children.head.scope
    val minVal = evalNum(o.scope(min, o.lines)).toEInt(o.lines).i
    val maxVal = evalNum(o.scope(max, o.lines)).toEInt(o.lines).i
    val strideVal = evalNum(o.scope(stride, o.lines)).toEInt(o.lines).i
    val body = o.children(0)
    val indSym = childScope.unique(index)

    for (n <- minVal until maxVal by strideVal) {
      setValue(indSym, implicitCast(EInt(n), Index()))
      evalInner(body).map(v => return Some(v))
    }
    None
  }

  def evalWhile(o: TypedLoAst, w: While): Option[EVal] = {
    val body = o.children(0)
    while (evalBool(o.scope(w.cond, o.lines)).b) {
      val retval = evalInner(body)
      retval.map(v => return Some(v))
    }
    None
  }


  def evalPrefixSum(o: TypedLoAst, ps: PrefixSum): Option[EVal] = {
    // Just translate into equivalent LoRes code, and then evaluate that.
    val acc = tempIds.newId("acc")
    val tmp = tempIds.newId("tmp")
    val i   = tempIds.newId("i")
    val arr = ps.arr
    val arrRef = addrOf(o.exprChildren.head)
    val earr = arrRef.value.toEArray(o.lines)
    val Pair(start, end) = evalArrOpRange(o, earr.len, ps.range)
    val len = end - start
    val intType = o.scope(ps.opArr.sub(0), o.lines).loType
    val code = {
      DecAssign(acc, intType, Const(0)) +
      DecAssign(tmp, intType, Const(0)) +
      ForBlock(i, len,
        (tmp := arr.sub(start+i)) +
        (arr.sub(start+i) := acc) +
        (acc := acc + tmp))
    }
    val top = TypedLoAst(code, Some(o.scope))
    evalInner(top)
  }

  def evalArrOpRange(
      o: TypedLoAst,
      arrLen: Int,
      range: Option[ArrOpRange]): Pair[Int, Int] = {
    val Pair(start, end) = range match {
      case Some(r) => {
        val start = evalNum(o.scope(r.start, o.lines)).toEInt(o.lines).i.toInt
        val end = evalNum(o.scope(r.end, o.lines)).toEInt(o.lines).i.toInt
        Pair(start, end)
      }
      case None => Pair(0, arrLen-1)
    }
    val len = end - start
    if (len > arrLen || start < 0 || end > arrLen) {
      val errStr = s"Array range ($start, $end) out of bounds in array of length $arrLen"
      throw InterpError(errStr, o.lines)
    }
    Pair(start, end)
  }

  def evalRotate(
      o: TypedLoAst,
      lv: LValue,
      shamt: Expr,
      range: Option[ArrOpRange],
      left: Boolean): Option[EVal] = {
    val arrRef = addrOf(o.exprChildren.head)
    val arr = arrRef.value.toEArray(o.lines)
    val shamtInt = evalNum(o.exprChildren(1)).toEInt(o.lines).i.toInt
    val Pair(start, end) = evalArrOpRange(o, arr.len, range)
    val len = end - start
    val dir = if(left) { shamtInt } else { len-shamtInt }
    val newArr = (0 until arr.len) map {
      i => {
        if(i >= start && i < end)
          arr.a(start + ((dir+i) % len))
        else
          arr.a(i)
      }
    }
    arrRef.value = EArray(newArr.toArray, arr.len)
    None
  }

  def evalReverse(o: TypedLoAst, rv: Reverse): Option[EVal] = {
    val arrRef = addrOf(o.exprChildren.head)
    val arr = arrRef.value.toEArray(o.lines)
    val Pair(start, end) = evalArrOpRange(o, arr.len, rv.range)
    val len = end - start
    val newArr = (0 until arr.len) map {
      i => {
        if(i >= start && i < end)
          arr.a(start + len - i - 1)
        else
          arr.a(i)
      }
    }
    arrRef.value = EArray(newArr.toArray, arr.len)
    None
  }

  def evalMemset(o: TypedLoAst, ms: Memset): Option[EVal] = {
    val i = tempIds.newId("i")
    val value = tempIds.newId("value")
    val arr = ms.arr
    val arrRef = addrOf(o.exprChildren.head)
    val earr = arrRef.value.toEArray(o.lines)
    val Pair(start, end) = evalArrOpRange(o, earr.len, ms.range)
    val len = end - start
    val code = {
      DecAssign(value, o.scope(ms.value, o.lines).loType.toPrimitive, ms.value) +
      ForBlock(i, len, arr.sub(start+i) := value)
    }
    evalInner(TypedLoAst(code, external = Some(o.scope)))
  }

  def evalEqual(et: TypedExpr, eq: Equal): Boolean = {
    et.scope(eq.e1, et.lines).loType match {
      case iv: IntValued => {
        val cmpRes = evalNum(et.scope(eq.e1, et.lines)).compare(evalNum(et.scope(eq.e2, et.lines)))
        cmpRes == 0
      }
      case Bool(_) => evalBool(et.scope(eq.e1, et.lines)).b == evalBool(et.scope(eq.e2, et.lines)).b
      case Ptr(_, _) => {
        evalPtr(et.children(0)).ref == evalPtr(et.children(1)).ref
      }
      case NullType => {
        evalPtr(et.children(0)).ref == evalPtr(et.children(1)).ref
      }
      case t => throw InterpError(s"Equality check not implemented for type $t", et.lines)
    }
  }

  def evalNum(et: TypedExpr, toType: Option[NonRec]=None): ENumber = {
    lazy val err = s"${et.expr} of type ${et.loType} is not number-valued in ${et.scope.altToString}"
    val scope = et.scope
    def binOp(n1: ENumber, n2: ENumber)
            (fi: (EInt, EInt) => EInt)
            (ff: (EFloat, EFloat) => EFloat)
            (fd: (EDouble, EDouble) => EDouble): ENumber = toType.getOrElse(et.loType) match {
      case (d: LoDouble) => fd(n1.toEDouble(et.lines), n2.toEDouble(et.lines))
      case (f: LoFloat) => ff(n1.toEFloat(et.lines), n2.toEFloat(et.lines))
      case (i: IntValued) => fi(n1.toEInt(et.lines), n2.toEInt(et.lines))
      case _ => throw InterpError(err, et.lines)
    }
    def unOp(n: ENumber)(fi: EInt => EInt)(ff: EFloat => EFloat)(fd: EDouble => EDouble): ENumber = {
      toType.getOrElse(et.loType) match {
        case (d: LoDouble) => fd(n.toEDouble(et.lines))
        case (f: LoFloat) => ff(n.toEFloat(et.lines))
        case (i: IntValued) => fi(n.toEInt(et.lines))
        case _ => throw InterpError(err, et.lines)
      }
    }
    et.expr match {
      case Const(i) => unOp(EInt(i))(n=>n)(n=>n)(n=>n)
      case FloatConst(f) => EFloat(f)
      case DoubleConst(d)=> EDouble(d)
      case Cast(e, loType) => cast(evalInner(et.children.head), loType).toENumber(et.lines)
      case Escape(e, from, to, f) => implicitCast(f(evalInner(et.children.head)).toENumber(et.lines), to).toENumber(et.lines)
      case Neg(e)        => unOp(evalNum(et.children.head))(-_)(-_)(-_)
      case Minus(e1, e2) => binOp(evalNum(et.children(0)), evalNum(et.children(1)))(_-_)(_-_)(_-_)
      case Plus(e1, e2) => binOp(evalNum(et.children(0)), evalNum(et.children(1)))(_+_)(_+_)(_+_)
      case Mul(e1, e2) => binOp(evalNum(et.children(0)), evalNum(et.children(1)))(_*_)(_*_)(_*_)
      case Div(e1, e2) => binOp(evalNum(et.children(0)), evalNum(et.children(1)))(_/_)(_/_)(_/_)
      case ShiftLeft(e1, e2) => binOp(evalNum(et.children(0)), evalNum(et.children(1)))(_<<_)((_, _) => ???)((_, _) => ???)
      case ShiftRight(e1, e2) => binOp(evalNum(et.children(0)), evalNum(et.children(1)))(_>>_)((_ , _)=> ???)((_, _) => ???)
      case Mod(e1, e2)   => evalNum(et.children(0)).toEInt(et.lines) % evalNum(et.children(1)).toEInt(et.lines)
      case Pow(e1, e2)   => binOp(evalNum(et.children(0)), evalNum(et.children(1)))(_.pow(_))(_.pow(_))(_.pow(_))
      case Pow2(exp) => unOp(evalNum(scope(exp, et.lines)))(_.pow2)(_.pow2)(_.pow2)
      case Log2Up(n) => unOp(evalNum(scope(n, et.lines)))(_.log2Up)(_ => ???)(_ => ???)
      case NumEntries(e) => evalNumEntries(et.children.head)
      case LowerWord(e) => evalLowerWord(et.children.head)
      case Size(texpr) => evalSize(texpr)
      case m @ Mux(cond, e1, e2) => evalInner(et).toENumber(et.lines)
      case BitAnd(e1, e2) => binOp(evalNum(et.children(0)), evalNum(et.children(1)))(_ & _)((_,_) => ???)((_,_) => ???)
      case BitRange(e, msbExpr, lsbExpr) => {
        val msb = evalNum(et.children(1)).toEInt(et.lines)
        val lsb = evalNum(et.children(2)).toEInt(et.lines)
        evalInner(et.children(0)) match {
          case ei: EInt => (ei.range(lsb, msb))
          case other => EInt(other.toEBits(et.lines).bits.intValue)
        }
      }
      case lval: LValue => {
        val lv = addrOf(et).value
        lv match {
          case n: ENumber => n
          case ENoVal => throw new InterpError(s"Use of uninitialized value in expression ${et.expr}", et.lines, true)
          case other => throw InterpError(s"[$other] $err", et.lines)
        }
      }
      case Safe(e1) => evalNum(et.children.head, toType)
      case _ => throw InterpError(err, et.lines)
    }
  }


  def evalBool(et: TypedExpr): EBool = {
    val scope = et.scope
    val boolRes = et.expr match {
      case True => true
      case False => false
      case Mux(cond, e1, e2) => evalInner(et).toEBool(et.lines).b
      case And(e1, e2) => evalBool(et.children(0)).b && evalBool(et.children(1)).b
      case Or(e1, e2) => evalBool(et.children(0)).b || evalBool(et.children(1)).b
      case Not(e1) => !(evalBool(et.children(0)).b)
      case Less(e1, e2) => evalNum(et.children(0)).compare(evalNum(et.children(1))) < 0
      case LessEq(e1, e2) => evalNum(et.children(0)).compare(evalNum(et.children(1))) <= 0
      case Greater(e1, e2) => evalNum(et.children(0)).compare(evalNum(et.children(1))) > 0
      case GreaterEq(e1, e2) => evalNum(et.children(0)).compare(evalNum(et.children(1))) >= 0
      case eq @ Equal(e1, e2) => evalEqual(et, eq)
      case lval: LValue => {
        addrOf(et).value match {
          case EBool(b) => b
          case ENoVal => throw new InterpError(s"Use of uninitialized value in expression ${et.expr}", et.lines, true)
          case other => throw InterpError(s"${et.expr} [$other] is not a Bool in ${et.scope.altToString}", et.lines)
        }
      }
      case Safe(e1) => evalBool(et.children.head).b
      case _ => throw InterpError(s"${et.expr} is not a boolean expression", et.lines)
    }
    EBool(boolRes)
  }

  def evalPtr(et: TypedExpr): EPtr = {
    et.expr match {
      case Ref(lval) => EPtr(addrOf(et.children.head))
      case m @ Mux(cond, e1, e2) => evalInner(et).toEPtr(et.lines)
      case lval: LValue => addrOf(et).value.toEPtr(et.lines)
      case Safe(e1) => evalPtr(et.children.head)
      case Null => EPtr(ENull)
      case _ =>
        throw InterpError(
          s"${et.expr} [${et.loType}] is not a Ptr type in ${et.scope.altToString}",
          et.lines)
    }
  }

  def evalRecord(et: TypedExpr): ERecord = {
    et.expr match {
      case lval: LValue => addrOf(et).value.toERecord(et.lines)
      case Safe(e1) => evalRecord(et.children.head)
      case _ =>
        throw InterpError(
          s"${et.expr} [${et.loType}] is not a Record type in ${et.scope.altToString}",
          et.lines)
    }
  }

  def evalNumEntries(et: TypedExpr): EInt = {
    lazy val err = {
      InterpError(s"${et.expr} [${et.loType}] is not a container type in ${et.scope.altToString}", et.lines)
    }
    val evalue = et.expr match {
      case lval: LValue => addrOf(et).value
      case _ => throw err
    }
    evalue match {
      case EArray(_, len) => EInt(len)
      case _ => throw err
    }
  }

  def evalLowerWord(lw: TypedExpr): EInt = {
    def makeWord(ev: EVal): EInt = {
      EInt(
        ev.toEBits(lw.lines).bits.intValue,
        widthBytes=4,
        signed=false)
    }

    lw.expr match {
      case BitRange(e, msbExpr, lsbExpr) => {
        val msb = evalNum(lw.children(1)).toEInt(lw.lines)
        val lsb = evalNum(lw.children(2)).toEInt(lw.lines)
        evalInner(lw.children(0)) match {
          case ei: EInt => (ei.range(lsb, msb))
          case other => makeWord(other).range(lsb, msb)
        }
      }
      case _ => {
        evalInner(lw) match {
          case ei: EInt => (ei)
          case other => makeWord(other)
        }
      }
    }
  }

  def evalSize(loType: LoType): EInt = EInt(1)
  //  The reported sizes don't actually matter in the interpreter, so just
}

object LoInterp {
  def apply(
      vars: Map[SymLike, EVal],
      scope: Symtab=Symtab.Empty,
      ec: Option[LoInterp]=None): LoInterp = {
    val ctx = new LoInterp()
    for((k, v) <- vars) { 
      val ref = new EAddr(v)
      ctx.values(ScopedSym(k, scope.getEnclosing(k))) = ref
    }
    ctx
  }

  /** Returns a new [[TypedLoAst]] where all [[Field]]s have been replaced by [[UField]]s
    *
    * This is a performance optimization for the interpreter, as either hashing or searching
    * string-based field names has proven to be too expensive in many use cases.
    */
  def ufieldsOnly(typed: TypedLoAst): TypedLoAst = {
    def trans(typed: TypedLoAst): LoAst = {
      def transExpr(e: TypedExpr): Expr = {
        val newCh = e.expr.replaceChildren(e.children.map(transExpr))
        newCh match {
          case Field(l, name) => {
            val indices: Map[String, Int] = e.children.head.loType match {
              case s: Struct => Map(s.fields.map(_._1.name).zipWithIndex:_*)
              case r: Record => Map(r.namedFields.map(_._1).zipWithIndex.toSeq:_*)
              case t: TypeRef => {
                val struct = typed.scope(t.name).loType.toStruct
                Map(struct.fields.map(_._1.name).zipWithIndex:_*)
              }
              case other => throw new AssertionError(s"Can't handle $other")
            }
            UField(l, indices(name.name), Some(name))
          }
          case other => other
        }
      }
      val newCh = typed.ast.replaceAstChildren(typed.children.map(trans))
      newCh.replaceExprChildren(typed.exprChildren.map(transExpr))
    }
    val newAst = trans(typed)
    TypedLoAst(newAst, withListing=true)
  }
}
