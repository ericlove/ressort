// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo
import ressort.compiler.cpp._

/** Collection of methods to translate each kind of [[LoAst]] node into a 
  * corresponting [[CppAst]] node.
  *
  * Methods for specific node types can be overridden by subclasses used to, for example,
  * insert appropriate OpenMP pragmas where desired.
  *
  * @param initBuffers Inserts initialiation to zero code at each buffer allocation.
  *                     This may improve performance for large buffers if it results
  *                     in superpage promotion on some operating systems.
  *
  * @param irAstToCppAst C++ AST generator. Different platforms will choose this
  *                       differently: for example, parallel platform will translate
  *                       [[ressort.lo.ForPar]] differently.
  */
class LoAstToCppAst(
    initBuffers: Boolean=false,
    addRestrict: Boolean=true,
    arrOpTranslator: CppArrOpTranslator = new CppArrOpTranslator(),
    loopTranslator: CppLoopTranslator = new CppLoopTranslator()) {

  // needed by loopTranslator methods
  private implicit val irAstToCppAst = this

  /** Returns a C++ [[Expr]] from an LoRes [[lo.Expr]] */ 
  def transExpr(e: lo.Expr)
      (implicit ast: lo.TypedLoAst): Expr = {
    // In the current scheme, expression translation never needs to be
    // overridden or altered
    Expr(ast.scope(e))
  }

  /** Saves a re-used value as a constant, returns it along with a declaration.
    *
    * Use case: LoRes For loop semantics differ from C's in that the loop 
    * conditions (max, etc.) aren't re-evaluated every iteration.
    */
  def constParam(e: lo.Expr, name: String)
      (implicit ast: lo.TypedLoAst): (Expr, Option[Dec]) = {
    e match {
      case lo.Const(n) => (Const(n), None)
      case other => {
        val tmp = TmpId(name)
        val cppExpr = Some(transExpr(e))
        val dec = Dec(tmp, SizeT(const=true), cppExpr)
        (tmp, Some(dec))
      }
    }
  }

  /** Returns the C++ version of an LoRes [[lo.TypedLoAst]]
    *
    * This is the method that [[CppLoTranslator]] should call to obtain
    * a [[CppAst]] from type-checked LoRes code.  It dispatches the different
    * node types to their corresponding methods in the [[LoAstToCppAst]]
    * intereface; to change translation behavior, derived classes should
    * override those functions individualy.
    */
  final def trans(ir: lo.TypedLoAst): CppAst = {
    implicit val ast = ir
    ast.ast match {
      case b: lo.Block => transBlock(b)
      case d: lo.Dec => transDec(d)
      case a: lo.Assign => transAssign(a)
      case da: lo.DecAssign => transDecAssign(da)
      case ha: lo.HeapAlloc => transHeapAlloc(ha)
      case f:  lo.Free => transFree(f)
      case p: lo.Prefetch => transPrefetch(p)
      case ar: lo.AssignReturn => transAssignReturn(ar)
      case f: lo.ForLoopLoAst => loopTranslator.translate(f)
      case fd: lo.FuncDec => transFuncDec(fd)
      case a: lo.App => transApp(a)
      case om: lo.OutputMatch => transOutputMatch(om)
      case ie: lo.IfElse => transIfElse(ie)
      case w: lo.While => transWhile(w)
      case lo.Nop => Nop
      case td: lo.Typedef => transTypedef(td)
      case r: lo.Return => transReturn(r)
      case aop:lo.ArrOp => arrOpTranslator.translate(ast, aop)
      case pf: lo.Printf => transPrintf(pf)
      case f: lo.FakeLoAst => transFakeLoAst(f)
      case other => transOther(other)
    }
  }

  def transBlock(b: lo.Block)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    Block(ast.children map trans)
  }

  def transAssign(a: lo.Assign)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    Assign(transExpr(a.l), transExpr(a.e))
  }

  def transWhile(w: lo.While)
    (implicit ast: lo.TypedLoAst): CppAst = {
      
    While(transExpr(w.cond), trans(ast.children(0)))
  }

  def transDec(d: lo.Dec)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    val cppType = CppType(d.loType)
    Dec(Id(d.v.name), cppType, None) 
  }

  def transDecAssign(da: lo.DecAssign)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    val cppType = CppType(da.loType)
    Dec(Id(da.sym.name), cppType, Some(transExpr(da.value)))
  }

  def transTypedef(td: lo.Typedef)
      (implicit ast: lo.TypedLoAst): StructDec = {
    try {
      StructDec(td.name.name, td.fields map { 
          case (f, t) => (f.name -> CppType(t))
        })
    } catch {
      case ae : AssertionError => {
        val err = "Error in checking typedef " + td + ": "+ae
        throw new AssertionError(err)
      }
    }
  }

  def transPrefetch(pf: lo.Prefetch)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    Prefetch(Ref(transExpr(pf.l)))
  }

  def transHeapAlloc(ha: lo.HeapAlloc)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    ast.scope(ha.l).loType match {
      case lo.Ptr(lo.Arr(scalarLoType, _), _) if ha.length.nonEmpty => {
        val cppType = CppType(scalarLoType)
        val cppExpr = transExpr(ha.length.get)
        val cppLValue = transExpr(ha.l)
        val memset = {
          CallStmt(
            Call(Id("memset"), 
              List(DerefDot(cppLValue, "pointer"), Const(0), Mul(Sizeof(cppType), cppExpr))))
        }
        val alloc = {
          Assign(cppLValue, Alloc(Vector(cppType), List(cppExpr)))
        }

        if (initBuffers) Block(List(alloc,memset)) else alloc
      }
      case lo.Ptr(loType, _) => {
        Assign(transExpr(ha.l),  Alloc(CppType(loType)))
      }
      case _ => ???
    }
  }

  def transFree(f: lo.Free)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    val loType = ast.scope(f.l).loType
    val lvExpr = transExpr(f.l)
    Free(lvExpr)
  }

  def transAppExpr(app: lo.App)
      (implicit ast: lo.TypedLoAst): Expr = {
    val newArgs = app.args.toList map { case (v, e)  => transExpr(e) }
    Call(Id(app.func.name), newArgs)
  }

  def transApp(a: lo.App)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    CallStmt(transAppExpr(a).asInstanceOf[Call])
  }

  def transFuncDec(fd: lo.FuncDec)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    val cppReturnCppType = fd.returnType match {
      case Some(pt) => CppType(pt)
      case None => Void
    }
    Func(
      Id(fd.name.name), 
      cppReturnCppType,
      fd.params map { p => Id(p._1.name) -> CppType(p._2) },
      trans(ast.children(0)))
  }

  def transIfElse(ie: lo.IfElse)
      (implicit ast: lo.TypedLoAst): CppAst = {
         
    val ifStmt = trans(ast.children(0))
    val elseStmt = ie.elseBody match {
      case lo.Nop => None
      case _ => Some(trans(ast.children(1)))
    }
    IfElse(transExpr(ie.cond), ifStmt, elseStmt)
  }

  def transOther(other: lo.LoAst)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    Comment("<<" + other.toString.filter(_ != '\n') + ">>")
  }

  def transReturn(r: lo.Return)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    Return(transExpr(r.expr))
  }

  def transAssignReturn(ar: lo.AssignReturn)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    Assign(transExpr(ar.l), transAppExpr(ar.a))
  }

  def transPrintf(pf: lo.Printf)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    (Printf(pf.fmt, (pf.e map { transExpr(_) }):_* ))
  }

  def transOutputMatch(om: lo.OutputMatch)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    throw new Error("OutputMatch currently unsupported in C++")
  }

  def transFakeLoAst(f: lo.FakeLoAst)
      (implicit ast: lo.TypedLoAst): CppAst = {
        
    Block(ast.children map { trans(_) })
  }
}
