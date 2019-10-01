package ressort.lo.compiler
import ressort.lo._

/** Transforms nodes of an Expr AST and/or accumulates information
  * from depth-first traversal of that AST.
  */
abstract class ExprTransform { 
  /** Type of payload data to pass upwards during depth-first traversal. */
  type T

  /** Contains an already-transformed child node and its accompanying
    * payload while transforming parent.
    */
  case class XFormExpr(newExpr: Expr, payload: T)

  /** Performs main transformation on all nodes in the expression AST. */
  def trans(
    e: Expr,
    children: List[XFormExpr],
    scope: Symtab): XFormExpr

  /** Handles AST's root node separately from the rest.
    *
    * Some transforms may optionally implement this function to handle
    * the AST's root separately.  Those that do must explicitly call
    * trans() in their own transTopNode if they want to also apply
    * the same transformation to the root as to the others.
    */
  def transRoot(
    e: Expr,
    children: List[XFormExpr],
    scope: Symtab): XFormExpr = trans(e, children, scope)


  def dfTransHelper(e: Expr, scope: Symtab=Symtab.Empty): XFormExpr = {
    trans(e, e.children map { c => dfTransHelper(c, scope) }, scope)
  }
  def dfTrans(e: Expr, scope: Symtab=Symtab.Empty): XFormExpr = {
    val xfExpr = dfTransHelper(e, scope)
    transRoot(e, e.children map { c => dfTransHelper(c, scope) }, scope)
  }

  /** Applies this [[ExprTransform]] to each node in the Op tree.
    *
    * Child classes of [[TypedLoAstTransform]] should call this at the beginning
    * of their `trans()` implementations to make use of [[ExprTransforms]].
    */
  def transExprs(ast: LoAst, scope: Symtab): LoAst = {
    implicit def fromXForm(xfe: XFormExpr): Expr = xfe.newExpr
    def trans(e: Expr) = dfTrans(e, scope)

    ast.replaceExprChildren(ast.exprChildren.map(trans(_)).map(_.newExpr))
  }

  /** Returns a new Expr as a result of replacing a node's children
    * with the new Exprs in the children list.
    *
    * @param e Expr whose children are to be replaced
    * @param children List of XFormExprs from applying this transform
    *                 node e's children.  Number and order of XFormExprs
    *                 must exactly match linear order of Expr arguments to
    *                 e's constructor.
    */
  def replaceChildren(e: Expr, children: List[XFormExpr]) = {
    val chl = children map { _.newExpr }
    e.replaceChildren(chl)
  }

}

object ReplaceExprs {
  private def trans(e: Expr): Expr = {
    val newChildren = e.replaceChildren(e.children.map(trans))
    val newExpr = newChildren match {
      case Plus(Const(a), Const(b)) => Const(a+b)
      case Pow2(Const(a)) => Const(1 << a)
      case Plus(Plus(Const(a1), a2), Plus(Const(b1), b2)) => {
        Plus(Const(a1+b1), Plus(a2, b2))
      }
      case Plus(a, Const(0)) => a
      case Plus(Const(0), a) => a
      case Minus(a, Const(0)) => a
      case Mul(a, Const(1)) => a
      case Mul(Const(1), a) => a
      case Minus(Const(a), Const(b)) => Const(a-b)
      case Mul(Const(a), Const(b)) => Const(a*b)
      case Div(Const(a), Const(b)) => Const(a/b)
      case Neg(Const(a)) => Const(-a)
      case Pow(Const(a), Const(b)) => Const(math.pow(a, b).toInt)
      case Mod(Const(a), Const(b)) => Const(a % b)
      case BitRange(Const(a), Const(msb), Const(lsb)) => {
        require(lsb >= 0 && lsb <= 31)
        require(msb >= 0 && msb <= 31)
        require(lsb <= msb)
        val mask = (1L << (msb-lsb+1)) - 1L
        Const(((a >> lsb) & mask).toInt)
      }
      case Less(Const(a), Const(b)) => {
        if (a < b) True else False
      }
      case Greater(Const(a), Const(b)) => {
        if (a > b) True else False
      }
      case Mux(True, e, _) => e
      case Mux(False, _, e) => e
      case other => other
    }
    newExpr
  }

  def apply(e: Expr): Expr = trans(e)
}
