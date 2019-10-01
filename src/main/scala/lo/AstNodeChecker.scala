// See LICENSE.txt
package ressort.lo
import ressort.util._
import TypedLoAst.AstCheckRes



/** Performs type-checking for a given kind of AST node:
  *
  * Each node type implements a subclass of [[AstNodeChecker]], filling
  * in the check function to produce an AstCheckRes.
  * Base class handles type-checking of children, assembling any resulting
  * errors; child class must just check its own node.
  */
abstract class AstNodeChecker {
  import ExprChecker._
  import TypedLoAst._

  /** Symtab for normal identifiers */
  val scope: Symtab

  /** Symtab for funcs and typedefs */
  val globals: Symtab

 /** Type guaranteed to be returneed by this node  */
  val retType: Option[Primitive]

  /** The AST of this node itself.
    *
    *  Note that subclasses should refine this to their specific node type */
  val ast: LoAst

  /** The source listing lines corresponding to this node, if one exists */
  val lines: Option[LoAstLines]

  /** Scopes in which each child AST node will be checked
    *
    * For example: a for loop will map its induction variable to UInt
    * for checking the body, while if-else statments will allocate a new
    * [[Symtab]] for each side.
    */
  def childScopes: Seq[Symtab]

  /** globals in which all child Ops and Exprs will be type-checked. */
  def childGlobals: Symtab

  /** True if this node is contained within a [[FuncDec]]
    *
    * This determines whether declarations add to the global scope.
    */
  def inFunc: Boolean

  /** Return type of scope enclosing this nodes children.
    * 
    * Note that actual cehcking of return types is handled by 
    *   (1.) The CheckReturn object (checks if return expr is a Primitive)
    *   (2.) The CheckFuncDec object (checks its body's return matches spec)
    */
  def childRetType: Option[Primitive] = None

  /** Returns AstCheckResult from checking of local node after checking
    * of children has been handled by the base class.
    */
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes

  /** True iff the this node is a [[FuncDec]] or it is contained inside one */
  lazy val childInFunc: Boolean = inFunc || ast.isInstanceOf[FuncDec]

  lazy val childExprsCheckRes: List[ECheckRes] = {
    assert(lines.nonEmpty)
    ast.exprChildren.map(scope.exprChecker(_, lines))
  }

  /** Returns errors for any [[TypeRef]]s contained in `loType` not found in scope */
  def missingTypeRefErrors(loType: LoType): List[AstCheckErr] = {
    loType match {
      case TypeRef(s, _) if scope.symType(s).isEmpty => {
        val errMsg = s"Unresolved reference to type $s"
        AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil
      }
      case s: Struct => s.fields.map(f => missingTypeRefErrors(f._2)).toList.flatten
      case a: Arr => missingTypeRefErrors(a.elementType)
      case p: Ptr => missingTypeRefErrors(p.loType)
      case f: Func => {
        val plist: List[AstCheckErr] = f.params.map(f => missingTypeRefErrors(f._2)).toList.flatten
        val rlist: List[AstCheckErr] = f.retType.map(missingTypeRefErrors(_)).toList.flatten
        plist ++ rlist
      }
      case _ => Nil
    }
  }

  def result(implicit allowFakeAst: Boolean): AstCheckRes = {
    val childExprErrs = {
      childExprsCheckRes.flatMap(_.left.toOption getOrElse Nil)
    }
    val typedExprChildren = for {
      (e, res) <- ast.exprChildren.zip(childExprsCheckRes)
    } yield res match {
      case Right(texpr) => texpr
      case _ => new TypedExpr(e, NoType, scope, Nil, lines)
    }

    // If there are any type errors from this node's expressions,
    // generate a single OpCheckErr describing them.
    val exprErr: List[AstCheckErr] = if(childExprErrs isEmpty) {
      Nil
    } else {
      val errMsgs = childExprErrs map { 
        e => s"In expression [${e.expr}]:\n"+
        indent(e.err) + "\n"
      }
      val err = s"${reduceNewline(errMsgs).take(800)}\n"
      val errMsg = lines match {
        case Some(lines) =>
          s"On line ${lines.start}:\n$err"
        case None =>
          s"In op:\n${ast.tabStr(3)}\n$err"
      }
      List(AstCheckErr(ast, lines, scope, globals, errMsg))
    }
    val childAstNodesCheckRes = {
      // Produce the list of children in reverse order, so the last
      // child is always the head of the list during the reduction.
      var revRes = List[AstCheckRes]()
      val children = ast.astChildren
      val childLines = lines.map(_.children.map(Some(_))).getOrElse(children.map(c => None))
      assert(children.length == childScopes.length)
      assert(children.length == childLines.length)
      for (((cast, cscope), clines) <- children.zip(childScopes).zip(childLines)) {
        revRes = checkAst(cast, clines, cscope, childGlobals, childInFunc, childRetType) :: revRes
      }
      revRes.reverse
    }
    val childAstErrs = childAstNodesCheckRes.flatMap(_.left.toOption getOrElse Nil)
    val typedAstChildren = for {
      res <- childAstNodesCheckRes 
    } yield res match {
      case Right(tast) => tast
      // Comment this out for now, because of the increase in spurious errors
      // when it is enabled.  TODO: Figure out a better filtering mechanism.
      //case Left(err::t) => {
      //  TypedLoRes(err.ast, Nil, scope, globals)
      //}
      case _ => return Left(exprErr ++ childAstErrs)
    }

    // Have derived class perform its own Op-specific type check for this node
    val nodeCheckRes = check(typedExprChildren, typedAstChildren) match {
      case Left(l: List[AstCheckErr]) if lines.nonEmpty => {
        // Make sure to add line numbers to the error message if they're available
        Left(l.map(a => a.copy(errMsg = s"On lines ${lines.get.start} -- ${lines.get.end}:\n${a.errMsg}")))
      }
      case other => other
    }
    
    val nodeErrs = if (typedExprChildren.map(_.loType).contains(NoType)) {
      // If at least on child expr is type NoType, don't report any
      // node-level type checking errors, since we've already found at least
      // on an want to avoid an explosion of spurious errors.
      Nil
    } else {
      (nodeCheckRes.left.toOption getOrElse Nil)
    }

    val errs = exprErr ++ nodeErrs ++ childAstErrs
    if(errs isEmpty) nodeCheckRes else Left(errs)
  }
}



case class CheckForLoop(
    ast: ForLoopLoAst,
    lines: Option[LoAstLines],
    scope: Symtab, 
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  val childScopes = {
    val child = new Symtab(Some(scope), retType)
    child.add(ast.index, Index(const=true))
    List(child)
  }
  def childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val minType = typedExprChildren(0).loType
    val maxType = typedExprChildren(1).loType
    val strideType = typedExprChildren(2).loType
    val body = typedAstChildren(0)

    var typeErrs: List[AstCheckErr] = Nil

    def checkIntParam(e: Expr, eType: LoType, name: String): Unit = {
      if(!Index().accepts(eType)) {
        val errMsg = {
          s"Expression [$e] of type ${eType} used for loop $name; "+
          s"int-valued type expected.\n"
        }
        typeErrs = AstCheckErr(ast, lines, scope, globals, errMsg) :: typeErrs
      } 
    }

    checkIntParam(ast.min, minType, "min")
    checkIntParam(ast.max, maxType, "max")
    checkIntParam(ast.stride, strideType, "stride")

    if (typeErrs.isEmpty)
      Right(new TypedLoAst(ast, lines, body::Nil, typedExprChildren, scope, globals, body.retType))
    else
      Left(typeErrs)
  }
}


case class CheckBlock(
    ast: Block,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  def childScopes = ast.astChildren.map(c => scope)
  def childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    if (typedAstChildren isEmpty)
      return Right(new TypedLoAst(ast, lines, Nil, Nil, scope, globals, None))

    val retTypes = typedAstChildren.flatMap(_.retType)
    val bodyRetType = if(retTypes isEmpty) None else Some(retTypes(0))
    Right(new TypedLoAst(ast, lines, typedAstChildren, Nil, scope, globals, bodyRetType))
  }
}

case class CheckAssign(
    ast: Assign,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  def childScopes = Nil
  def childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val lvType = typedExprChildren(0).loType
    val eType = typedExprChildren(1).loType
    if(lvType.accepts(eType))
      Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals, None))
    else {
      val errMsg = {
        s"Attempt to assign expression [${ast.e}] of type $eType "+
        s"to lvalue [${ast.l}] of type ${lvType}.\n"
      }
      Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
    }
  }
}

case class CheckDecAssign(
    ast: DecAssign,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  def childScopes = Nil
  def childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val loType = ast.loType
    val valType = typedExprChildren.head.loType
    val refErrs = missingTypeRefErrors(loType)

    if (refErrs.nonEmpty) {
      Left(refErrs)
    } else if (!loType.nonConst.accepts(valType)) {
      val errMsg = {
        s"Attempt to assign expression [${ast.value}] of type $valType "+
        s"to new variable ${ast.sym} with declared type $loType.\n"
      }
      Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
    } else {
      scope.add(ast.sym, loType)
      Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals))
    }
  }
}
    
      

case class CheckPrefetch(
    ast: Prefetch,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  def childScopes = Nil
  def childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals, None))
  }
}

case class CheckIfElse(
    ast: IfElse,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  val childScopes = ast.astChildren.map(c => new Symtab(parent = Some(scope), returnType = retType))
  def childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val condType = typedExprChildren.head.loType
    val ifBody = typedAstChildren(0)
    val elseBody = typedAstChildren(1)
    val retTypes = typedAstChildren.map(_.retType)
    val nodeRetType = if(retTypes(0) == (retTypes(1))) retTypes(0) else None
    if(!Bool().accepts(condType)) {
      val errMsg = {
        s"Condition expression [${ast.cond}] in if statement "+
        s"is of type ${condType}; Bool expected.\n"
      }
      Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
    } else {
      Right(new TypedLoAst(ast, lines, typedAstChildren, typedExprChildren, scope, globals, nodeRetType))
    }
  }
}

case class CheckReturn(
    ast: Return,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  def childScopes = Nil
  def childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val eType = typedExprChildren.head.loType

    if(eType.isInstanceOf[Primitive]) {
      // We don't check the return type here; just pass it up as the return
      // type of this node, and the base checker will compare it to retType.
      Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals, Some(eType.toPrimitive)))
    } else {
      val errMsg = {
        s"Attempt to return [$ast.e] of type $eType, which is not a Primitive.\n"
      }
      Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
    } 
  }
}

case class CheckHeapAlloc(
    ast: HeapAlloc,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  def childScopes = Nil

  def childGlobals = globals

  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val lvType = typedExprChildren(0).loType
    val lenType = ast.length.map(_ => typedExprChildren(1).loType)

    val err = (lvType, lenType) match {
      case (Ptr(Arr(t2, _), _), Some(i: IntValued)) => None
      case (Ptr(Arr(t2, _), _), _) => {
        Some(s"Int-type length required for allocation of array type Arr($t2); $lenType found.\n")
      }
      case (_, Some(lt)) => Some(s"Length supplied for non-array pointer type $lvType")
      case (Ptr(_, _), None) => None
      case (_, _) => Some(s"Attempting to allocate non-pointer type $lvType")
    }
    err match {
      case Some(errMsg) => Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
      case _ =>
        Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals))
    }
  }
}

case class CheckFree(
    ast: Free,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive])
  extends AstNodeChecker {
  def childScopes = Nil
  def childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals))
  }
}

case class CheckDec(
    ast: Dec,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  val childScopes = Nil
  val childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val loType = ast.loType
    val refErrs = missingTypeRefErrors(loType)
    if (refErrs.isEmpty) {
      scope.add(ast.v, loType)
      Right(new TypedLoAst(ast, lines, Nil, Nil, scope, globals))
    } else {
      Left(refErrs)
    }
  }
}


case class CheckFuncDec(
    ast: FuncDec,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  val childScopes = {
    val cscope = if (inFunc) globals else scope
    val child = new Symtab(Some(cscope), ast.returnType)
    ast.params.map(p => child.add(p._1, p._2))
    List(child)
  }
  val childGlobals = globals
  
  // Needed so that any Return()s inside the body will be compared 
  // against this type.
  override val childRetType = ast.returnType
  
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val body = typedAstChildren(0)
    val retTypeErr: List[AstCheckErr] = {
      (ast.returnType, body.retType) match {
        case (None, None) => Nil
        case (Some(decType), Some(bodyType)) if(!decType.accepts(bodyType)) => {
          val errMsg = {
            s"Returning type $bodyType "+
            s"from function with return type $decType.\n"
          }
          AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil
        }
        case (None, Some(body)) => {
          val errMsg = {
            s"Returning type $body where no return expected.\n"
          }
          AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil
        }
        case (Some(dec), None) => {
          val errMsg = {
            s"Function body does not return any value; "+
            s"return of type $dec expected.\n" +
            body
          }
          AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil
        } 
        case _ => Nil
      }
    }
    
    if(retTypeErr isEmpty) {
      val ftype = Func(ast.params, ast.returnType)
      scope.add(ast.name, ftype)
      Right(new TypedLoAst(ast, lines, typedAstChildren, Nil, scope, globals))
    } else {
      Left(retTypeErr)
    }
  }
}


case class CheckApp(
    ast: App,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  val childScopes = Nil
  val childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val funcTypeRes = scope.typeOfFunc(ast.func)
    val argTypes = typedExprChildren.map(_.loType)

    // Check that the identifier in the App is (1.) defined and (2.) a function
    if (funcTypeRes.isEmpty) {
      val errMsg = s"Function ${ast.func} is undefined. $ast\n" + scope.altToString + "\n-\n" + globals.altToString
      return Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
    }
    val funcType = funcTypeRes.get

    // Make sure the number of actual parameters equals number of formal params
    if (ast.args.toList.length != funcType.params.toList.length) {
      val formal = funcType.params.toList.length
      val actual = ast.args.toList.length
      val name = ast.func.name
      val proto = s"Function Type:\n${indent(funcType.toString, 3)}\n"
      val errMsg = s"$actual arguments given to $name; $formal expected;\n$proto"
      return Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
    }
    
    val argList = ast.args.map(_._2).toList
    val argErrs = (argTypes zip funcType.params).zipWithIndex collect {
      case ((argType, (param, paramType)), i) if (!paramType.accepts(argType)) => {
        val arg = argList(i)
        val errMsg = {
          s"Passing expression [${arg}] of type ${argType} "+
          s"to parameter $param of type $paramType.\n"
        }
        AstCheckErr(ast, lines, scope, globals, errMsg)
      }
      case ((argType, (param, paramType)), i) if (ast.args.toList(i)._1 != param) => {
        val argName = ast.args.toList(i)._1
        val errMsg = {
          s"Parameter $i of name $argName does not match parameter name $param in $ast"
        }
        AstCheckErr(ast, lines, scope, globals, errMsg)
      }
    } 

    if (argErrs isEmpty)
      Right(new TypedLoAst(ast, lines, typedAstChildren, typedExprChildren, scope, globals))
    else
      Left(argErrs)
  }
}



  


case class CheckAssignReturn(
    ast: AssignReturn,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  val childScopes = List(scope)
  val childGlobals = globals
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val lvType = typedExprChildren.head.loType
    val app = typedAstChildren.head.ast.toApp
    val funcTypeRes = scope.typeOfFunc(app.func)

    if (funcTypeRes isEmpty) {
      val errMsg = s"Function ${app.func} undefined.\n"
      return Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
    }
    val funcType = funcTypeRes.get
    val funcRetType = funcType.retType

    funcRetType match {
      case None => {
        val errMsg = {
          s"Assigning return value from function [$app], "+
          s"which does not return any value.\n"
        }
        Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
      }
      case Some(t) if (!lvType.accepts(t)) => {
        val errMsg = {
          s"Assigning result of function [$app] "+
          s"of type $t "+
          s"to LValue [${ast.l}] of type $lvType.\n"
        }
        Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
      }
      case _ => Right(new TypedLoAst(ast, lines, typedAstChildren, typedExprChildren, scope, globals))
    }
  }
}


case class CheckTypedef(
    ast: Typedef,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  val childScopes = Nil
  val childGlobals = globals

  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    if (scope.symType(ast.name).nonEmpty || globals.symType(ast.name).nonEmpty) {
      val errMsg =
        s"Attempting to define type ${ast.name}, " +
        s"which is already defined as ${scope(ast.name)}"
      Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
    } else {
      scope.add(ast.name, ast.struct)
      Right(new TypedLoAst(ast, lines, Nil, Nil, scope, globals))
    }
  }
}
    
case class CheckWhile(
    ast: While,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  val childScopes = List(scope.child())
  val childGlobals = globals

  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val condType = typedExprChildren.head.loType
    val body = typedAstChildren.head
    
    if (!Bool().accepts(condType)) {
      val errMsg = {
        s"Condition expression [${ast.cond}] in while loop "+
        s"has type $condType; Bool expected.\n"
      }
      Left(AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil)
    } else {
      Right(new TypedLoAst(ast, lines, typedAstChildren, typedExprChildren, scope, globals, body.retType))
    }
  }
}


case class CheckPrintf(
    ast: Printf,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends AstNodeChecker {
  val childScopes = Nil
  val childGlobals = globals

  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    // TODO: actually type-check against format string
    Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals))
  }
}

case class CheckFakeLoAst(
    ast: FakeLoAst,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive])
  extends AstNodeChecker {

  def childScopes = ast.astChildren.map(_ => new Symtab(Some(scope), retType))
  def childGlobals = globals

  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    Right(new TypedLoAst(ast, lines, typedAstChildren, typedExprChildren, scope, globals))
  }
}

case class CheckUseSym(
    ast: UseSym,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive])
    extends AstNodeChecker {

  def childScopes = Nil
  def childGlobals = globals

  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    Right(new TypedLoAst(ast, lines, typedAstChildren, typedExprChildren, scope, globals))
  }
}

/** Handles type-checking tasks common to all ArrOps.
  *
  * Checks the arr LValue and optional ArrOpRange argument.
  * Assumes canonical ordering of ArrOp constructor arguments
  * as defined by the ArrOp base class's exprChildren {} implementation.
  */
abstract class ArrOpChecker extends AstNodeChecker {
  val ast: ArrOp

  def childScopes = Nil
  def childGlobals = globals

  def checkRange(typedExprChildren: List[TypedExpr]): List[AstCheckErr] = {
    if (ast.opRange == None)
      return Nil
    val range = ast.opRange.get
    val rangeTypes = typedExprChildren.reverse.slice(0,2).map(_.loType) // start, end
    val rangeExprs = range.start :: range.end :: Nil

    for {
      (e, t) <- rangeExprs zip rangeTypes
      if (!Index().accepts(t) && !UInt().accepts(t))
    } yield {
      val errMsg = {
        s"Expression [$e] of non-int type $t "+
        s"used in start or end of array op range."
      }
      AstCheckErr(ast, lines, scope, globals, errMsg)
    }
  }

  def checkArr(typedExprChildren: List[TypedExpr]): List[AstCheckErr] = {
    val arrType = typedExprChildren.head.loType
    arrType match {
      case Arr(_, _) => Nil
      case _ => {
        val errMsg = {
          s"Attempting to apply array op to LValue [${ast.opArr}] "+
          s"of non-array type $arrType.\n"
        }
        AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil
      }
    }
  }
}


case class CheckRot(
    ast: ArrOp,  // could be either RotLeft or RotRight
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends ArrOpChecker {
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val shamt = ast match {
      case RotLeft(_, shamt, _) => shamt
      case RotRight(_, shamt, _) => shamt
      case _ => throw new AssertionError("Can't happen")
    }
    val shamtType = typedExprChildren(1).loType
    val shamtErr = shamtType match {
      case iv: IntValued => Nil
      case other => {
        val errMsg = {
          s"Expression [$shamt] of non-int type $other "+
          s"used as shift amount in array rotate.\n"
        }
        AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil
      }
    }

    val errs = {
      shamtErr ++ 
      checkArr(typedExprChildren) ++
      checkRange(typedExprChildren)
    }
  
    if (errs isEmpty)
      Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals))
    else 
      Left(errs)
  }
}

case class CheckReverse(
    ast: Reverse,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends ArrOpChecker {
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val errs = {
      checkArr(typedExprChildren) ++
      checkRange(typedExprChildren)
    }
  
    if (errs isEmpty)
      Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals))
    else 
      Left(errs)
  }
}

case class CheckPrefixSum(
    ast: PrefixSum,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends ArrOpChecker {
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val arrType = typedExprChildren.head.loType
    val nonIntErr = arrType match {
      case Arr(t, _) if (!t.isInstanceOf[IntValued]) => {
        val errMsg = {
          s"Cannot peform prefix sum operation of array of non-int type $t.\n"
        }
        AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil
      }
      case _ => Nil
    }


    val errs = {
      nonIntErr ++
      checkArr(typedExprChildren) ++
      checkRange(typedExprChildren)
    }
  
    if (errs isEmpty)
      Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals))
    else 
      Left(errs)
  }
}


case class CheckMemset(
    ast: Memset,
    lines: Option[LoAstLines],
    scope: Symtab,
    globals: Symtab,
    inFunc: Boolean,
    retType: Option[Primitive]) extends ArrOpChecker {
  def check(typedExprChildren: List[TypedExpr], typedAstChildren: List[TypedLoAst]): AstCheckRes = {
    val arrErrs = checkArr(typedExprChildren)
    if (!arrErrs.isEmpty)
      return Left(arrErrs)
    val scalarType = typedExprChildren(0).loType match {
      case Arr(t, _) => t
      case _ => throw new AssertionError(s"Applying Memset() to non-array in $ast")
    }
    val valType = typedExprChildren(1).loType

    val valTypeErr = if (!scalarType.accepts(valType)) {
      val errMsg = {
        s"Cannot Memset() array [${ast.opArr}] of element type $scalarType "+
        s"with value [${ast.value}] of type $valType.\n"
      }
      AstCheckErr(ast, lines, scope, globals, errMsg) :: Nil
    } else {
      Nil
    }

    val errs = {
      valTypeErr ++
      checkArr(typedExprChildren) ++
      checkRange(typedExprChildren)
    }

    if (errs isEmpty)
      Right(new TypedLoAst(ast, lines, Nil, typedExprChildren, scope, globals))
    else 
      Left(errs)
  }
}
