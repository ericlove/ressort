// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._


abstract class TypedLoAstTransform {
  type T
  /** A "transformed AST" contains the new version of a node in an LoRes AST
    * (`newAst`) and an transform-specific payload type used to aggregate
    * information from the node's children.
    */
  case class XFormAst(newAst: LoAst, payload: T)
  
  def trans(ast: TypedLoAst, children: List[XFormAst]): XFormAst

  /** The child class' implementation of trans() can either choose to replace
    * the ast by a new one with children from prior recursive calls to trans(),
    * or leave it as is.  This function is called in the former case.
    */
  def replaceChildren(ast: LoAst, newChildren: List[XFormAst]): LoAst = {
    val chList = newChildren map { _.newAst }
    ast.replaceAstChildren(chList) 
  }


  // Depth-first transform
  def dfTrans(ast: TypedLoAst): XFormAst = {
    trans(ast, ast.children map { dfTrans _ })
  }

  /** Apply an ExprTransform to each node in the Op tree.
    *
    * Child classes of TypedLoAstTransform should call this at the beginning
    * of their trans() implementations to make use of ExprTransforms.
    */
  def transExprs(et: ExprTransform, ast: LoAst, scope: Symtab): LoAst = {
    // TODO: delete this when ready to replace all calls elsewhere
    et.transExprs(ast, scope)
  }
}
