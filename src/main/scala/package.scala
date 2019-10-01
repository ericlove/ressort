package ressort
import lo.LoAst

package object util  {
  /** Returns a properly JVM-formatted Long from one read out of a binary file
    *
    * Take an integer from Source.readInt and convert it to a Long without
    * sign extending.  Reverse byte order if from little endian source
    */
  def ULongFromInt(rawInt: Integer)(
    implicit isLittleEndian:Boolean=false): Long = {
    // No unsigned ints in JVM...make sure not to sign-extend int to long
    val mask = 0xffffffffL 
    val bigEndian: Integer = {
      if(isLittleEndian)
        java.lang.Integer.reverseBytes(rawInt)
      else
        rawInt
    }
    mask & bigEndian
  }

  def paramStr[A](l: Traversable[A]): String = l.mkString(", ")
  
  def indent(str: String, tabs: Integer=1) = {
    val lines = str.split("\n") map {
      line => ("  "*tabs)+line
    }
    lines.mkString("\n")
  }

  def indent(ast: LoAst): String = ast.lines(3).toString

  def escape(raw: String): String = {
    "\"" + raw.replace("\n", "\\n").replace("\t", "\\t") + "\""
  }

  def reduceNewline(lines: Traversable[String]): String = {
    lines.foldLeft("") { (set, line) => set+line+"\n" }
  }

  def log2Up(n: Int): Int = math.ceil(math.log(n)/math.log(2.0)).toInt

}

package object hi {
  implicit def idOpFromSymbol(s: Symbol): Operator = IdOp(Id(s.name))

  implicit def idFromSymbol[T >: Id](s: Symbol): T = Id(s.name)

  implicit def idFromProgSym[T <: ProgSym](s: T): Id = s.id

  implicit def idOpFromProgSym[T <: ProgSym](s: T): Operator = IdOp(s.id)

  implicit def idListFromSymbol(sseq: Seq[(Symbol, Data)]): Seq[(Id, Data)] = {
    sseq.map { case (s, t) => Id(s.name) -> t }
  }

  implicit def idPairFromSymbol[D <% Data](sid: (Symbol, D)): (Id, Data) = {
    (Id(sid._1.name) -> sid._2)
  }

  implicit def projectionFromSymbols[T <% Expr](p: (Symbol, T)): (Id, Expr) = (p._1, p._2)

  implicit def constFromInt[T >: Const](n: Int): T = Const(n)

  implicit def floatConstFromFloat[T >: FloatConst](f: Float): T = FloatConst(f)

  implicit def doubleConstFromDouble[T >: DoubleConst](d: Double): T = DoubleConst(d)

  implicit def anonymousField(t: lo.NonRec): lo.Record.Field = {
    lo.Record.Field(loType = t, name = None)
  }

  implicit def toPayload(p: lo.Primitive): Payload = Payload(p)

  implicit def namedField(sid: (Symbol, lo.NonRec)): lo.Record.Field = {
    lo.Record.Field(sid._2, Some(sid._1))
  }

  implicit def seqToGroup(s: Seq[lo.Record.Field]): lo.Record.Group = {
    lo.Record.Group(fields = s:_*)
  }

  implicit def primSeqToGroup(s: Seq[lo.NonRec]): lo.Record.Group = {
    lo.Record.Group(fields = s.map(lo.Record.Field(_)):_*)
  }

  implicit def aggFieldFromSym(p: (Symbol, CommutativeOp)): (FieldName, CommutativeOp) = (NFieldName(p._1), p._2)
  implicit def symbolToFieldName(s: Symbol): FieldName = NFieldName(s)
  implicit def idToFieldName(i: Id): NFieldName = NFieldName(i)
  implicit def intToFieldName(i: Int): UFieldName = UFieldName(i)
  implicit def fieldNameToExpr(fn: FieldName): Expr = fn match {
    case UFieldName(i) => UField(i)
    case NFieldName(i) => i
  }
}


package object lo {
  implicit def exprFromInt(n: Int): Expr = Const(n)

  type TmpVarFunc = String => Id
  def symbolToId(s: Symbol)(implicit tmpVars: TmpVarFunc = { Id(_) }): Id = {
    tmpVars(s.name)
  }
    
  object Err {
    def illegalFuncType(t: hi.HiType) = {
      "Cannot translate HiRes Func type "+t+" into LoRes equivalent."
    }
    def illegalTypeTrans(t: hi.HiType) = {
      "Cannot translate HiRes type "+t+" into LoRes equivalent."
    }
  }

  implicit def SymbolPrimitiveToIdPrimitive(sp: (Symbol, Primitive)): (Id, Primitive) = {
    (symbolToId(sp._1) -> sp._2)
  }

  implicit def SymbolToId[T >: Id](s: Symbol): T = symbolToId(s)
  
  implicit def SymbolSymbolToIdId[T1 >: Id, T2 >: Id](ss: (Symbol, Symbol)): (T1, T2) = {
    (symbolToId(ss._1) -> symbolToId(ss._2))
  }

  implicit def SymbolIntToIdExpr(si: (Symbol, Int)): (Id, Expr) = {
    (symbolToId(si._1) -> Const(si._2))
  }
 
  implicit def SymbolTToIdExpr[T <% Expr](st: (Symbol, T)): (Id, Expr) = {
    (symbolToId(st._1) -> st._2)
  }

  implicit def SymbolLoTypeToIdLoType[T <% LoType](si: (Symbol, T)): (Id, T) = {
    (symbolToId(si._1) -> si._2)
  }

  implicit def SymbolToType(s: Symbol): LoType = TypeRef(s)

  implicit def anonymousField(t: lo.NonRec): lo.Record.Field = {
    lo.Record.Field(loType = t, name = None)
  }
}
