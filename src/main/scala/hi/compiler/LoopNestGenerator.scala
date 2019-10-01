// See LICENSE.txt
package ressort.hi.compiler
import ressort.lo._
import scala.collection.mutable.{HashMap, LinkedHashSet}

/** Result of LoRes code generation for a particular `HiRes` operator.
  *
  * This result will either  be inserted into a larger loop nest by the
  * [[ressort.hi.compiler.LoopNestGenerator]], or taken as-is if it
  * is the outermost loop of a DAG node.
  *
  * @param body Code for the innermost loop
  * @param initializer Code to be placed __before__ the innermost loop
  * @param higherInit Code to be placed one level higher than `initializer`
  * @param finalizer Code to be placed __after __ the innermost loop
  */
case class LoopLevel(
    body:         LoAst,
    allocation:   LoAst=Nop,
    deallocation: LoAst=Nop,
    initializer:  LoAst=Nop,
    higherInit:   LoAst=Nop,
    finalizer:    LoAst=Nop,
    builder:      Option[LoAst=>LoAst]=None) {

  def build(nextBody: LoAst): LoAst = {
    val res = builder.map(b => b(nextBody)).getOrElse(body + nextBody)
    res
  }

  /** Result of fusing `this` with `other` (in that order) */
  def +(other: LoopLevel): LoopLevel = {
    LoopLevel(
      body = build(other.body),
      initializer = this.initializer + other.initializer,
      higherInit = this.higherInit + other.higherInit,
      finalizer = this.finalizer + other.finalizer,
      allocation = this.allocation + other.allocation,
      deallocation = this.deallocation + other.deallocation,
      builder = Some(ast => build(other.build(ast))))
  }

  /** Returns a copy with `ast` appended to `body` __and__ a new builder that
    * always appends it.
    */
  def +(ast: LoAst): LoopLevel = {
    def newBuilder(nextBody: LoAst): LoAst = this.build(nextBody) + ast
    this.copy(body = this.body + ast, builder = Some(newBuilder))
  }

  /** Returns a copy with `ast` prepended to `body` __and__ a new builder that
    * always prepends it.
    */
  def prepend(ast: LoAst): LoopLevel = {
    def newBuilder(nextBody: LoAst): LoAst = ast + this.build(nextBody)
    this.copy(body = ast + this.body, builder = Some(newBuilder))
  }

  def mergedBody: LoopLevel = {
    this.copy(
      body = initializer + body + finalizer,
      higherInit = Nop,
      initializer = higherInit,
      finalizer = Nop,
      builder = None)
  }
}

/** Generates nested loops for the specified node */
class LoopNestGenerator(node: LoDag, elaboration: Elaboration) {

  private val isNestedReduction     = node.op.isNestedReduction
  private val isInternalReduction   = node.op.isInternalReduction
  private val lastLevelLoop         = node.op.lastLevelLoop
  private val dataParallelOutput    = node.op.dataParallelOutput
  private val controlsOutputCursor  = node.op.controlsOutputCursor
  private val dynamicAllocation     = node.op.dynamicAllocation
  private val skipElaboration       = node.op.skipElaboration
  private val arrayNestingChange    = node.op.arrayNestingChange
  private val lowersNestingLevel    = node.op.lowersNestingLevel
  private val nonFusable            = node.op.nonFusable
  private val skipLoopLevels        = node.op.skipLoopLevels
 
  /** Array that controls the innermost scan-leading cursor */
  private val leader: ArrayView = {
    if (node.inputViews.nonEmpty)
      node.inputViews.head
    else
      node.outputView
  }

  import ressort.hi

  /** Emits nested loops around `inner`, the result of a [[CodeGenerator]] */
  def emitNestedLoops(inner: LoopLevel): LoopLevel = {
    import ressort.hi
    if (skipElaboration)
      return LoopLevel(Nop)

    // Keep modifying this var to build a new inner loop
    var newInner = inner

    // Declare any immaterial (scalarized) buffers allocated by this node
    newInner = newInner.prepend(node.localAlloc)

    // Output cursors are updated for every window -- that is, as the last statement
    // of the innermost loop.
    if (controlsOutputCursor && node.outputView.vectorCursor.nonEmpty) {
      val cur = node.outputView.vectorCursor.get
      val initOutputCursor: LoAst = {
         DecAssign(cur, Index(), Const(0))
      }
      val setNumValid: LoAst = node.outputView.accessNumValid.map(_ := cur).getOrElse(Nop)
      if (lowersNestingLevel)
        newInner = newInner.copy(higherInit = newInner.higherInit + initOutputCursor)
      else
        newInner = newInner.copy(initializer = newInner.initializer + initOutputCursor)
      newInner += setNumValid
    } else {
      val numValidInput = {
        // If no cursor update, copy the num valid from this node's controlling input
        val control = node.internalDag.map(_.outputView).getOrElse(leader)
        control match {
          case n: NestedView if lowersNestingLevel => n.base.accessNumValid
          case _ if lowersNestingLevel => None
          case _ => control.accessNumValid
        }
      }
      val nvUpd = (numValidInput, node.outputView.accessNumValid) match {
        case (Some(in), Some(out)) => (out := in)
        case _ => Nop
      }
      newInner += nvUpd
    }

    // Not every node gets a last level loop (e.g. those inside fused segments)
    val controlled =
        leader.vectorCursor
          .map(node.ownCursors.contains(_))
          .getOrElse(false)
    if (lastLevelLoop && controlled) {
      val loop = {
        val cursor = leader.vectorCursor.get
        val max = leader.maxCursor
        val state = elaboration.states.globalState(cursor)
        if (dataParallelOutput) {
          state + IPar(cursor, max, newInner.body)
        } else {
          state + ForBlock(cursor, max, newInner.body)
        }
      }
      newInner = newInner.copy(body = loop).mergedBody
    }

    // Recursively add outer loops
    newInner = 
      loopNest(
          leader    = leader,
          inner     = newInner,
          loopDepth = 0)

    newInner
  }


  /** Returns the accessor to use as the leader for the next level of loop
    * generation, or `None` if this is the last level.
    */
  private def nextLeader(
      leader: ArrayView,
      loopDepth: Int): Option[ArrayView] = {
    leader match {
      case c: ChunkArray.ChunkView if (isInternalReduction && loopDepth == 0) => {
        // Handle this case specially because the ancillary is inside the inner view
        Some(c.base.counts)
      }
      case n: NestedView => {
        if (isInternalReduction && loopDepth == 0) {
          assert(
            n.ancillaries != Nil,
            "Trying to internal-reduce accessor with no ancillary:\n" + 
            node.op.hiOp.toString + "\n" +
            n.array.mkString(2))
          Some(n.ancillaries.head)
        } else {
          Some(n.base)
        }
      }
      case _ => None
    }
  }

  /** Recursively traverses the leader array of this node to generate
    * nested loops and appropriate array state declarations and updates
    *
    * @param loopDepth   Number of loop-generating layers encountered so far
    */
  private def loopNest(
      leader:     ArrayView,
      inner:      LoopLevel,
      loopDepth:  Int): LoopLevel = {

    // Progressively transform this into the next loop level
    var loop = inner

    lazy val cursor = leader.cursor.get

    // Any state updates that should appear inside the body of this loop, at the top, if one is added
    lazy val topStateUpdates = elaboration.states.localState(cursor)
    // Any state updates that should appear inside the body of this loop, at the bottom, if one is added
    lazy val bottomStateUpdates = elaboration.states.incrementLocalState(cursor)

    // Is a for loop added at this level?
    val skip = {
        (loopDepth == 0 && isInternalReduction) ||
        (loopDepth < skipLoopLevels)
    }

    val newLoop: Option[LoAst] = {
      leader match {
        case _ if skip => None
        case _ if !node.ownCursors.contains(cursor) => None
        case n: NestedView if n.parallel && !nonFusable => {
          Some(IPar(cursor, n.numArrays, topStateUpdates + loop.body + bottomStateUpdates))
        }
        case n: NestedView  => {
          Some(ForBlock(cursor, n.numArrays, topStateUpdates + loop.body + bottomStateUpdates))
        }
        case _ => None
      }
    }

    newLoop map { l =>
      val newInit =
        elaboration.states.globalState(cursor) +
          elaboration.states.resetLocalState(cursor)
      loop = loop.copy(initializer = loop.initializer + newInit)
      loop = loop.copy(body = l).mergedBody
    }

    // Recursively add more nesting, up to loopDepth
    val loops = nextLeader(leader, loopDepth) match {
      case None     => loop
      case Some(l)  => loopNest(l, loop, loopDepth + 1)
    }
    loops
  }
}

