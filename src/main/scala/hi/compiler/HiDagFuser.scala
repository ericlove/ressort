// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi
import scala.collection.mutable.{HashMap, LinkedHashSet}
import scala.collection.mutable

/** Modifies the given `HiArrayOp` HiDag to fuse specified cliques.
  *
  * @note the type of `dag` is [[DoublyLinkedDag]] to ensure mutability of each
  *       node's fields
  */
class HiDagFuser(
    cliques: Seq[HiClique],
    fusionDepth: Int,
    lastLevelLoop: Boolean,
    arrayGenerator: OutputArrayGenerator)
  extends HiDagTransform[Seq[FusedNode]] {
  import HiDagTransform._


  /** Performs operator fusion on `dag` */
  def updateDag(dag: HiDag): Seq[FusedNode] = {
    val origDagOrder = dag.depthFirst(n=>n).zipWithIndex.toMap

    // First, Cat() together all cliques' bottom nodes to have single outputs
    val catCliques = for (c <- cliques) yield {
      val outputs = c.externallyVisible.toList.sortWith(origDagOrder(_) < origDagOrder(_))
      if (debug) {
        println("ABOUT TO CAT")
        c.print()
        println(s"CAT.")
      }
      val (bottom, _) = HiDagTransform.catNodesAndMap(outputs.head, outputs.tail, c.interior)
      HiClique(c.interior + bottom)
    }

    if (debug) {
      for (c1 <- cliques) {
        for (c2 <- cliques.filter(_ != c1)) {
          for (n <- c1.interior) {
            lazy val c1str = c1.interior.map(n => s"$n ${n.op.hiOp}").mkString("\n")
            lazy val c2str = c2.interior.map(n => s"$n ${n.op.hiOp}").mkString("\n")
            assert(!c2.interior.contains(n), s"$n ${n.op.hiOp} duplicated:\n$c1str\n\n\n$c2str")
          }
        }
      }
    }

    // Replace all references to Cat()'d nodes with corresponding Uncat()s in cliques
    val newCliques = catCliques.filter(_.top.nonEmpty)

    // Recompute DAG order now that new nodes have been inserted
    val dagOrder = dag.depthFirstPre(n=>n).zipWithIndex.toMap
   
    // Turn each clique into a fused node
    val fused =
      newCliques
        .map(new SingleCliqueFusion(_, dagOrder, fusionDepth, lastLevelLoop, arrayGenerator))
        .map(_.fusedNode)
    fused
  }
}

private class SingleCliqueFusion(
    clique: HiClique,
    dagOrder: HiDag => Int,
    fusionDepth: Int,
    lastLevelLoop: Boolean,
    arrayGenerator: OutputArrayGenerator) {

  val cursor = new HiDag.Cursor()

  def debugln(s: String="") { }

  val top = clique.top
  val bottom = clique.bottom
  val output: HiDag = clique.bottom.head
  val outputArray = output.output
  debugln("-"*90)
  debugln(s"Fusion depth $fusionDepth; cursor $cursor")

  
  assert(clique.bottom.tail.isEmpty, { clique.print(); "err" })

  // Modify nodes *inside* the segment 
  debugln(s"Replacing segment ${clique.below.head.op.typed.o} - ${clique.bottom.head.op.typed.o} - ${clique.top.map(_.op.typed.o)}")
  // Replace references to this segment in the seenBy lists at other nodes
  for (n <- clique.above) {
    debugln(s"\t$n ${n.op.typed.o}")
    n.seenBy = n.seenBy map { child =>
      if (clique.interior.contains(child)) {
        fusedNode
      } else { 
        child
      }
    }
  }

  // Replace references to this segment in the input lists at other nodes
  for (n <- clique.below) {
    n.inputs = n.inputs map { i => 
      if (clique.interior.contains(i)) {
        fusedNode
      } else {
        i
      } 
    }
  }
  clique.bottom.map(_.seenBy = Nil)

  debugln("#"*90)

  assert(
    !clique.above.isEmpty,
    s"empty exterior for segment:\n${clique.bottom.head.op.typed.o}")
  
  lazy val fusedNode: FusedNode = {
    // Replace the top with virtual input nodes
    val (inputs, virtualInputs, cursors) = {
      val inputs = clique.above.toList.sortWith(dagOrder(_) < dagOrder(_))
      val cursors = output.cursors + (fusionDepth -> cursor)
      val vinputs = inputs.map(VirtualInput(_, cursor, cursors, clique, output, lastLevelLoop))
      val vmap = inputs.zip(vinputs).toMap
      for (n <- clique.interior) {
        n.inputs = for (i <- n.inputs) yield {
          vmap.get(i).getOrElse(i)
        }
      }
      (inputs, vinputs, cursors)
    }

    val rop = hi.DagOp()

    // Construct a new HiRes funcion type signature for the fused operator
    val funcType = {
      val fromType = {
        val maps = inputs.map(_.op.typed.funcType.from)
        maps.foldLeft(Map[hi.Id, hi.Data]()) { _ ++ _ }
      }
      val toType = output.op.typed.funcType.to
      hi.Func(fromType, toType)
    }


    val op = 
      HiArrayOp(
        materialInputs     = top.map(_.op.materialInputs).reduce { _ ++ _},
        arrayInputs         = top.map(_.op.arrayInputs).reduce { _ ++ _ },
        dataParallelOutput  = false,
        streamingOutput     = false,
        controlsOutputCursor= false,
        nonFusable          = false,
        lastLevelLoop       = lastLevelLoop,
        blockingOutput      = output.op.blockingOutput,
        typed               = hi.TypedHiResOp(rop, funcType, inputs.map(_.op.typed)),
        lowersNestingLevel  = clique.nestingLevelChange < 0,
        raisesNestingLevel  = clique.nestingLevelChange > 0)

    val res = new FusedNode(
        op_ = op,
        clique = clique,
        cursor = cursor,
        fusionDepth = fusionDepth,
        inputs_ = inputs,
        virtualInputs = virtualInputs, 
        output_ = outputArray,
        seenBy_ = output.seenBy,
        internalDag_ = Some(output),
        cursors_ = cursors,
        lastLevelLoop = lastLevelLoop,
        linkLoops = true)
    res.ownCursors += cursor
    res.regenerateFromInputs(arrayGenerator)
    debugln("-"*90)
    res
  }

  /** A birtual HiDag node that represents the output of `node` */
  class VirtualInput(
      op: HiArrayOp,
      cursor: HiDag.Cursor,
      output: MetaArray,
      seenBy: List[HiDag]=Nil,
      cursors: Map[Int, HiDag.Cursor]=Map())
    extends HiDag(op, Nil, output, Nil, seenBy, None, cursors) {

    override def regenerateFromInputs(arrayGenerator: OutputArrayGenerator): Unit = {
      // Do nothing, because this must be done by the enclosing FusedNode
    }
  }

  object VirtualInput {
    /** Used to make unique IDs for each virtual node */
    private var vnodeCount = 0

    /** Stores pre-made virtualizations of HiDag nodes to avoid duplication */
    private val cache = HashMap[HiDag, VirtualInput]()

    def apply(
        node: HiDag,
        cursor: HiDag.Cursor,
        cursors: Map[Int, HiDag.Cursor],
        clique: HiClique,
        bottom: HiDag,
        lastLevelLoop: Boolean): VirtualInput = {
      if (cache.contains(node))
        return cache(node)

      val newHiResOp = {
        val name = hi.Id(s"virt_${node.output.buffer.name.name}_$vnodeCount")
        vnodeCount += 1
        hi.IdOp(name)
      }

      val newHiArrayOp =
        HiArrayOp(
          typed               = node.op.typed.copy(o = newHiResOp),
          materialInputs      = node.inputs.map(_ => false),
          arrayInputs         = node.inputs.map(_ => false),
          dataParallelOutput  = true,
          skipElaboration     = true,
          streamingOutput     = true)


      val virtualOutput = {
        node.output.cloneRef()
      }

      val virtual = new VirtualInput(
        op          = newHiArrayOp,
        cursor      = cursor,
        output      = virtualOutput,  
        seenBy      = node.seenBy.filter(clique.interior.contains(_)),
        cursors     = cursors)

      cache(node) = virtual
      virtual
    }
  }
}


/** Tracks the old output and top nodes for a [[HiClique]]
  *
  * @param lastLevelLoop Indicates if the `lastLevelLoop` property should be
  *                       set for the resulting `HiArrayOp`.
  *
  * @param linkLoops  Indicates if [[ressort.hi.compiler.LinkedHiArray]]s
  *                   should be generated for virtualized inputs/outputs; if not,
  *                   then IOs will be generated with references to the original
  *                   nodes' base arrays.
  */
class FusedNode(
    var clique:               HiClique, 
    var cursor:               HiDag.Cursor,
    var fusionDepth:          Int,
    var op_ :                 HiArrayOp,
    var inputs_ :             List[HiDag],
    var virtualInputs:        List[HiDag],
    var output_ :             MetaArray,
    var seenBy_ :             List[HiDag],
    var internalDag_ :        Option[HiDag],
    var cursors_ :             Map[Int, HiDag.Cursor],
    var lastLevelLoop:        Boolean,
    var linkLoops:            Boolean)
  extends HiDag(op_, inputs_, output_, Nil, seenBy_, internalDag_, cursors_) {

  private def bottom = clique.bottom.head

  /** The node for which for loops are generated */
  private val head = virtualInputs.head

  lazy val virtualInputIndices = virtualInputs.zipWithIndex.toMap

  /** Regenerates this segment's internal virtual input nodes based on the 
    * actual inputs in `inputs`, and regenerates all outputs accordingly.
    */
  override def regenerateFromInputs(arrayGenerator: OutputArrayGenerator): Unit = {
    // First, regenerate the output array types of each virtual input node
    for (n <- virtualInputs) {
      val outerInput = inputs(virtualInputIndices(n))
      val orig = outerInput.output
      n.output = outerInput.output.cloneRef()
    }

    if (!lastLevelLoop || fusionDepth > 0) {
      ownCursors += cursor
      cursors += (fusionDepth -> cursor)
    }

    // Second, generate internal nodes' outputs based on them
    internalDag.get.depthFirst { n =>
      // Link internal DAGs at this fusion's depth level
      n.cursors += (fusionDepth -> cursor)
      n.regenerateFromInputs(arrayGenerator)
    }
    // Since regeneration will also modify the output of the enclosing node,
    // we need to update output_ and output as well.
    val newOutput = internalDag.get.output
    output_ = newOutput
    output = output_

    // If there is a last-level loop around the whole segment, then this is
    // a flat-array segment, and non-externally-visible arrays can be flattened
    // to scalars where possible.
    if (lastLevelLoop) {
      setControllingCursors()
      immaterialize()
    }

  }  


  /** Sets all internal nodes' `immaterial` attribute to true.
    *
    * Once the segment has been fused, we can assume any internal
    * allocations may be made immaterial, as they are not visible outside.
    * If they were, they would have been replaced by references during
    * output virtualization.
    */
  private def immaterialize(): Unit = {
    val vset = inputs.map(_.output.buffers).foldLeft(output.buffers) (_ ++ _)
    bottom.depthFirst { n =>
      n.allocations.map { buf =>
        if (!buf.mustMaterialize && !vset.contains(buf)) {
          buf.immaterial = true
          buf.allocate = true
        }
      }
    }
  }


  private def setControllingCursors(): Unit = {
    // Inside a fused operator, there is only one controlling base cursor...
    val cc = this.cursor
    ownCursors += cc

    def walk(n: HiDag) {
      n.cursors += (0 -> cc)
      n.inputs map walk
    }
    walk(bottom)
  }
}
