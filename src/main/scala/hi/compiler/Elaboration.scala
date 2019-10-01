package ressort.hi.compiler
import ressort.compiler._
import ressort.lo
import ressort.hi
import scala.collection.mutable.HashMap


case class ElaboratedOp(hiOp: hi.Operator, loop: LoopLevel)

class ElaboratedDag(
    val op:           ElaboratedOp,
    val inputs:       List[ElaboratedDag],
    val output:       ArrayView)
  extends OpDag[ArrayView, ElaboratedOp, ElaboratedDag] {

  def internalDag = None
}

/** Generates LoRes code to implement the operators specified by an allocated
  * Dag.
  */
object ElaboratedDag {
  def apply(dag: LoDag, config: CompilerConfig): ElaboratedDag = {
    val e = new Elaboration(dag, config = config)
    e.elaborate(dag, isOutput = true)
  }
}

/** Contains all context needed to elaborate the nodes of `dag` */
class Elaboration(
    val dag: LoDag,
    val tempIds: lo.TempIds = new lo.TempIds("_e_"),
    val config: CompilerConfig = CompilerConfig.DefaultConfig) {

  val states = new DagArrayStates(dag)

  /** Holds all pre-computed Dag node elaboations */
  private val cache = HashMap[LoDag, ElaboratedDag]()

  def elaborate(node: LoDag, isOutput: Boolean = false): ElaboratedDag = {
    if (cache.contains(node))
      return cache(node)

    val elabInputs = node.inputs map { n => elaborate(n, false) }
      
    if (node.op.skipElaboration) {
      val op = ElaboratedOp(hiOp = node.op.hiOp, LoopLevel(lo.Nop))
      return new ElaboratedDag(op, elabInputs, node.outputView)
    }

    // It is assumed that a single Dag node either has an internal Dag 
    // or an operator, but not both
    val innerLoop: LoopLevel = node.internalDag match {
      case None => {
        val lbg = new LoopBodyGenerator(elaboration = this, node = node)
        val elab = lbg.innerLoop
        elab.copy(allocation = elab.allocation)
      }
      case Some(inner)  => {
        val innerLoops = 
          elaborate(inner)
            .depthFirst(_.op.loop)
        innerLoops.foldLeft(innerLoops.head) { _ + _ }
      }
    }
  
    val outerLoop = {
      val nlg = new LoopNestGenerator(node, this)
      nlg.emitNestedLoops(innerLoop)
    }

    val loop = outerLoop.copy(allocation = outerLoop.allocation + node.allocation, deallocation = node.deallocation)

    val op = ElaboratedOp(node.op.hiOp, loop)

    // Set the internal Dag field to none, becuase we will have merged it
    // if there was one.
    val newNode = new ElaboratedDag(op, elabInputs, node.outputView)
    cache(node) = newNode
    newNode
  }

}

class DagArrayStates(dag: LoDag) {

  def localState(cursor: lo.SymLike): lo.LoAst = block(cursor) { a: ArrayView =>
    a match {
      case p: ParallelView => p.localState(cursor)
      case _ => lo.Nop
    }
  }

  def incrementLocalState(cursor: lo.SymLike): lo.LoAst = block(cursor) { a: ArrayView =>
    a match {
      case s: SequentialView => s.incrementLocalState
      case _ => lo.Nop
    }
  }

  def resetLocalState(cursor: lo.SymLike): lo.LoAst = block(cursor) { a: ArrayView =>
    a match {
      case s: SequentialView => s.resetLocalState
      case _ => lo.Nop
    }
  }

  def append(cursor: lo.SymLike): lo.LoAst = block(cursor) { a: ArrayView =>
    a match {
      case c: ChunkArray.ChunkView => c.append
    }
  }

  def globalState(cursor: lo.SymLike): lo.LoAst = block(cursor) { a =>
    a.globalState
  }

  private def block(cursor: lo.SymLike)(f: ArrayView => lo.LoAst) = {
    val stmts = viewsWithCursor.get(cursor).getOrElse(Set()).map(f).toList.filter(_ != lo.Nop)
    if (stmts.isEmpty)
      lo.Nop
    else
      lo.Block(stmts)
  }

  /** A map of cursors to [[ArrayView]]s in `dag` whose state depends on them */
  private lazy val viewsWithCursor: HashMap[lo.SymLike, Set[ArrayView]] = {
    val cmap = HashMap[lo.SymLike, Set[ArrayView]]()
    def walk(n: LoDag) {
      n.depthFirst { n =>
        n.internalDag.map(walk)

        val views = n.inputViews :+ n.outputView

        def walkView(v: ArrayView): Unit = {
          v.ancillaries.map(walkView)
          v match {
            case n: NestedView => walkView(n.base)
            case m: MultiArray.View => {
              walkView(m.head)
              m.tail.map(walkView)
            }
            case _ =>
          }
          v.cursor.map { c =>
            val set = cmap.getOrElse(c, Set[ArrayView]())
            cmap(c) = set + v
          }
        }

        if (!n.op.skipElaboration)
          views.map(walkView)
      }
    }
    walk(dag)
    cmap
  }
}
