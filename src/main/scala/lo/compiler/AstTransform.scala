// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._


abstract class AstTransform {
  /** Type of payload to be aggregated from each AST's child nodes */
  type T

  /** A "transformed Op" contains the new version of a node in an LoRes AST 
    * and n transform-specific payload type used to aggregate 
    * information from the node's children.
    *
    * @param newAst    New version of the AST node
    * @param payload  Data being aggregated at this node
    */
  case class XFormAst(newAst: LoAst, payload: T)
  
  def trans(ast: LoAst, children: List[XFormAst]): XFormAst

  /** Replaces this node's children with results of trans().
    *
    * The child class' implementation of trans() can either choose to replace
    * the ast by a new one with children from prior recursive calls to trans(),
    * or leave it as is.  This function is called in the former case.
    */
  def replaceChildren(ast: LoAst, newChildren: List[XFormAst]) = {
    val chList = newChildren map { _.newAst }
    ast.replaceAstChildren(chList)
  }

  /** Depth-first transform */
  def dfTrans(ast: LoAst): XFormAst = {
    trans(ast, ast.astChildren map { dfTrans _ })
  }

  
}
