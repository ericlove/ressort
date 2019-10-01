// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo
import ressort.lo.{LoAstListing, LoAstLines}
import scala.collection.mutable.HashMap

/** A tag to uniquely identify for loops */
class LoopRef

/** Represents a parallel for loop tagged with a uniquely-identifying
  * reference
  */
case class AnnotatedLoop(
    loop: lo.ForPar,
    ref: LoopRef)
  extends lo.FakeLoAst {

  override def lines(indent: Integer=0, listing: LoAstListing = new LoAstListing()): LoAstLines = {
    val start = listing.length
    val ind = tabstop * indent
    listing += s"${ind}AnnotatedLoop {"
    val children = loop.lines(indent+1, listing) :: Nil
    val end = listing.length
    listing += s"$ind}"
    LoAstLines(this, start = start, end = end, children = children, listing = listing)
  }

  override def astChildren = List(loop)

  override def replaceAstChildren(newChildren: List[lo.LoAst]): AnnotatedLoop = {
    this.copy(loop = newChildren.head.asInstanceOf[lo.ForPar])
  }
}

/** First pass in OpenMP C++ code generation: gathers information
  * about parallel for loops in a given [[ressort.lo.TypedLoAst]]
  *
  * ==Details==
  * More specifically, it performs the following functions:
  * $ - It replaces each [[lo.ForPar]] node instance with a
  *     [[AnnotatedLoop]] with a reference that uniquely identifies it
  * $ - It builds a data structure, `dominators`, that maps each
  *     [[AnnotatedLoop]] reference to a list of references to [[AnnotatedLoop]]s
  *     that __dominate__ it.
  */
class FindParallelLoopDominators extends TypedLoAstTransform {
  /** As a payload, pass up a list of all parallel for loops that
    * an AST node dominates
    */
  type T = List[LoopRef]

  /** Tracks the set of parallel for loops that dominate each
    * parallel for loop:
    * 
    * `dominators(r)` = list of references (`ref` member) of loops that 
    *                   dominate the loop with reference `r`
    */
  val dominators = HashMap[LoopRef, List[LoopRef]]()

  def trans(oldAst: lo.TypedLoAst, children: List[XFormAst]): XFormAst = {
    val dominatedFors = children.map(_.payload).flatten.toList
    val newChildrenAst = replaceChildren(oldAst.ast, children)
    newChildrenAst match {
      case fp: lo.ForPar => {
        makeAnnotatedLoop(newChildrenAst, fp, dominatedFors)
      }
      case other => XFormAst(newChildrenAst, dominatedFors)
    }
  }

  /** Returns an [[XFormAst]] containing a new [[AnnotatedLoop]] for the given
    * [[lo.ForPar]] parallel for loop, and the list of parallel for loops
    * it dominates.
    */
  def makeAnnotatedLoop(
      oldAst: lo.LoAst,
      fp: lo.ForPar,
      dominatedFors: List[LoopRef]): XFormAst = {
    val ll = AnnotatedLoop(fp, new LoopRef())
    addDominator(ll, dominatedFors)
    XFormAst(ll, ll.ref :: dominatedFors)
  }

  /** Adds `ll` as a dominator of all loops in `dominatedFors` */
  def addDominator(ll: AnnotatedLoop, dominatedFors: List[LoopRef]): Unit = {
    for (d <- dominatedFors) {
      if (dominators.contains(d))
        dominators(d) = ll.ref :: dominators(d)
      else
        dominators(d) = ll.ref :: Nil
    }
  }
}

object FindParallelLoopDominators {
  def apply(ast: lo.TypedLoAst): (lo.TypedLoAst, Map[LoopRef, List[LoopRef]]) = {
    val fpld = new FindParallelLoopDominators()
    val tast = lo.TypedLoAst(fpld.dfTrans(ast).newAst)
    (tast, fpld.dominators.toMap)
  }
}
