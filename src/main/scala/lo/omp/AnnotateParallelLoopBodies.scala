package ressort.lo.compiler
import ressort.lo
import ressort.lo.{LoAstListing, LoAstLines}
import ressort.util.indent
import scala.collection.mutable.HashMap

/** Replaces the [[LoAst]] body of a parallel for loop so that the
  * OpenMP translator can access information about that loop's enclosing
  * for loops, if any.
  *
  * @param body The `body` member of the [[lo.ForPar]] node enclosing this
  *               annotation
  * @param loop The [[LoopRef]] enclosing the parallel for loop
  * @param dominators A list of all [[LoopRef]]s that dominate this one
  * @param dominates A list of all [[LoopRef]]s that this node dominates
  */
case class AnnotatedLoopBody(
    body: lo.LoAst,
    loop: LoopRef,
    dominators: List[LoopRef],
    dominates:  List[LoopRef])
  extends lo.FakeLoAst {
  
  override def astChildren = List(body)

  override def replaceAstChildren(newChildren: List[lo.LoAst]): AnnotatedLoopBody = {
    this.copy(body = newChildren.head)
  }

  override def lines(indent: Integer=0, listing: LoAstListing = new LoAstListing()): LoAstLines = {
    val ind = tabstop * indent
    val start = listing.length
    listing += s"${ind}AnnotatedLoopBody($loop) {"
    val children = List(body.lines(indent+1, listing))
    val end = listing.length
    listing += s"${ind}}"
    LoAstLines(this, start = start, end = end, children = children, listing = listing)
  }
}


/** Replaces the `body` member of each [[lo.ForPar]] loop with a
  * [[AnnotatedLoopBody]] so that the OpenMP translator can use these annotations
  * when deciding how to translate a parallel for loop.
  *
  * @param dominatorMap Maps each labeled loop to the set of all loops that 
  *                     dominate it. Taken from a [[FindParallelLoopDominators]]
  */
class AnnotateParallelLoopBodies(
    dominatorMap: Map[LoopRef, List[LoopRef]])
  extends TypedLoAstTransform {

  implicit val allowFakeAst = true

  // Up-propagate a list of the loops that this one dominates
  type T = List[LoopRef]

  def trans(oldAst: lo.TypedLoAst, children: List[XFormAst]): XFormAst = {
    val dominates = (children.map(_.payload)).flatten
    val newChildrenAst = replaceChildren(oldAst.ast, children)
    val newAst = newChildrenAst match {
      case al: AnnotatedLoop => annotateBody(newChildrenAst, al, dominates)
      case other => newChildrenAst
    }
    XFormAst(newAst, dominates)
  }

  def annotateBody(
      oldAst: lo.LoAst,
      al: AnnotatedLoop,
      dominates: List[LoopRef]): lo.LoAst = {
    val dominators = dominatorMap.get(al.ref) getOrElse Nil
    val newBody = new AnnotatedLoopBody(
      body = al.loop.body,
      loop = al.ref,
      dominators = dominators,
      dominates = dominates)
    al.loop.copy(body = newBody)
  }
}

object AnnotateParallelLoopBodies {
  def apply(
      ast: lo.TypedLoAst,
      dominators: Map[LoopRef, List[LoopRef]]): lo.TypedLoAst = {
    val aplb = new AnnotateParallelLoopBodies(dominators)
    lo.TypedLoAst(aplb.dfTrans(ast).newAst)
  }
}
