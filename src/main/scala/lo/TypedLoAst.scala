package ressort.lo
import scala.collection.mutable.ArrayBuffer
import ressort.util._
import TypedLoAst.AstCheckRes

/** Returned from the LoRes AST checker upon checking a well-formed
  * AST node.
  *
  * @param children List of this AST node's children in the same linear
  *                 order as they appear in this node's constructor.
  * @param scope     All identifiers in scope of this [[LoAst]]
  * @param globals     All [[Func]]s and [[Typedef]]s in scope of this [[LoAst]]:
  *                 includes all scope context that should also be in scope
  *                 of any function body after this node
  * @param newScope  Scope of all Ops following this node in a block
  * @param newGlobals  [[Func]]/[[Typedef]] scope for all [[LoAst]]s after this one
  * @param retType  [[LoType]] this [[LoAst]] is ''guaranteed'' to return
  */
class TypedLoAst(
    val ast: LoAst,
    val lines: Option[LoAstLines],
    val children: List[TypedLoAst],
    val exprChildren: List[TypedExpr],
    val scope: Symtab,
    val globals: Symtab,
    val retType: Option[Primitive] = None)


/** Returned from the LoRes AST checker when it finds a particular error
  * (that is, checkAst will return a list of these on failure).
  */
case class AstCheckErr(
    ast: LoAst,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    errMsg: String) {
  override def toString: String = errMsg
}

object TypedLoAst {
  /** All AST type checks return either a [[TypedLoAst]] (on success),
    * or a list of [[AstCheckErr]]s on failure.
    */
  type AstCheckRes = Either[List[AstCheckErr], TypedLoAst]
  
  implicit def fromChecker(
      anc: AstNodeChecker)(
      implicit allowFakeAst: Boolean): AstCheckRes = anc.result

  def checkAst(
      ast: LoAst,
      lines: Option[LoAstLines],
      scope: Symtab = (new Symtab()),
      globals: Symtab = (new Symtab()),
      inFunc: Boolean = false,
      retType: Option[Primitive] = None)
      (implicit allowFakeAst: Boolean): AstCheckRes = {
    ast match {
      case d @ Dec(v, t) => CheckDec(d, lines, scope, globals, inFunc, retType)
      case ip @ ForSeq(_, _, _, _, _) => {
        CheckForLoop(ip, lines, scope, globals, inFunc, retType)
      }
      case fb @ ForPar(_, _, _, _, _) => {
        CheckForLoop(fb, lines, scope, globals, inFunc, retType)
      }
      case b @ Block(ops) => CheckBlock(b, lines, scope, globals, inFunc, retType)
      case a @ Assign(l, e) => CheckAssign(a, lines, scope, globals, inFunc, retType)
      case da @ DecAssign(id, te, v) => CheckDecAssign(da, lines, scope, globals, inFunc, retType)
      case p @ Prefetch(l) => CheckPrefetch(p, lines, scope, globals, inFunc, retType)
      case ie @ IfElse(_, _, _) => CheckIfElse(ie, lines, scope, globals, inFunc, retType)
      case Nop => Right(new TypedLoAst(Nop, lines, Nil, Nil, scope, globals))
      case ret @ Return(expr) => CheckReturn(ret, lines, scope, globals, inFunc, retType)
      case ha @ HeapAlloc(_,_) => CheckHeapAlloc(ha, lines, scope, globals, inFunc, retType)
      case f @ Free(_) => CheckFree(f, lines, scope, globals, inFunc, retType)
      case fd @ FuncDec(name, params, body, returnType) => {
        CheckFuncDec(fd, lines, scope, globals, inFunc, retType).result
      }
      case a @ App(func, args) => CheckApp(a, lines, scope, globals, inFunc, retType)
      case ar @ AssignReturn(l, a) => CheckAssignReturn(ar, lines, scope, globals, inFunc, retType)
      case td @ Typedef(Struct(name, fields, _)) => CheckTypedef(td, lines, scope, globals, inFunc, retType)
      case w @ While(cond, body) => CheckWhile(w, lines, scope, globals, inFunc, retType)
      case rl @ RotLeft(_, _, _) => CheckRot(rl, lines, scope, globals, inFunc, retType)
      case rr @ RotRight(_, _, _) => CheckRot(rr, lines, scope, globals, inFunc, retType)
      case r @ Reverse(_, _) => CheckReverse(r, lines, scope, globals, inFunc, retType)
      case ps @ PrefixSum(_, _) => CheckPrefixSum(ps, lines, scope, globals, inFunc, retType)
      case ms @ Memset(_, _, _) => CheckMemset(ms, lines, scope, globals, inFunc, retType)
      case pf: Printf => CheckPrintf(pf, lines, scope, globals, inFunc, retType)
      case us: UseSym => CheckUseSym(us, lines, scope, globals, inFunc, retType)
      case f: FakeLoAst => {
        if(!allowFakeAst)
          Left(AstCheckErr(ast, lines, scope, globals, s"FakeOp $f not allowed.\n") :: Nil)
        else
          CheckFakeLoAst(f, lines, scope, globals, inFunc, retType)
      }
      case _ => throw new AssertionError("should not happen")
    }
  }

  /** Returns a type-checked ast from an original [[LoAst]]
    *
    * Note that by default, no source code listing string is generated for `ast`, as this is an expensive
    * operation.  However, if a type-checking error arises, `apply` will re-call itself with `withListing`
    * set to true so that error messages can be associated with specific source lines.
    *
    * @param ast The [[LoAst]] to be typechecked
    * @param external A [[Symtab]] of symbols defined outside the scope of `ast`
    * @param withListing Causes a source code listing ([[LoAstLines]]) to be generated if set
    * @param allowFakeAst If true, this check will not give an error if [[FakeLoAst]]s are encountered
    * @return a [[TypedLoAst]] with all sub-nodes of `ast` type-checked, or throw an exception on error
    */
  def apply(ast: LoAst, external: Option[Symtab]=None, withListing: Boolean=true)
              (implicit allowFakeAst: Boolean=true): TypedLoAst = {
    val maxStr = 2000
    val indent = 3
    val lines = if (withListing) Some(ast.lines(indent)) else None
    def errMsg(errList: List[AstCheckErr], listing: LoAstListing): String = {
      s"Error(s) in checking LoRes code:\n${listing}\n\n"+
      reduceNewline(errList.map(_.toString)).take(maxStr)
    }
    val globs = external.map(_.child()).getOrElse(new Symtab())
    val checkRes = checkAst(ast, lines, scope = globs, globals = globs)(allowFakeAst=allowFakeAst)
    checkRes match {
      case Right(tast) => tast
      case Left(errList) if !withListing => {
        TypedLoAst(ast, external, withListing=true)
      }
      case Left(errList) => {
        throw new AssertionError(errMsg(errList, lines.get.listing))
      }
    }
  }
}