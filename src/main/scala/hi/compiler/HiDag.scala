// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi
import ressort.hi.DagOp
import ressort.lo

import scala.collection.mutable.HashMap

/** Internal abbreviation for te HiRes array op HiDag type
  *
  * @param op The operator for which this node generates code
  * @param inputs All nodes whose results are used directly by this one
  * @param output The [[MetaArray]] containing this node's result
  * @param allocations All buffers created by this node
  * @param seenBy All nodes who use this node's result directly
  * @param internalDag The output node of any [[HiDag]] contained within this one due to fusion
  * @param cursors Cursors assigned to some levels of this node by outer nodes or by this one
  * @param ownCursors Cursors generated at this node and contolled or "owned" by it
  */
class HiDag(
    var op         : HiArrayOp,
    var inputs     : List[HiDag],
    var output     : MetaArray,
    var allocations: List[Buffer],
    var seenBy     : List[HiDag]=Nil,
    var internalDag: Option[HiDag]=None,
    var cursors    : Map[Int, HiDag.Cursor]=Map(),
    var ownCursors : Set[HiDag.Cursor]=Set())
  extends DoublyLinkedDagLike[MetaArray, HiArrayOp, HiDag] {


    /** Regenerates `newNode`, its output arraay, and properties based on its current inputs.
      *
      * @param arrayGenerator The [[ressort.hi.compiler.OutputArrayGenerator]] used
      *                       by the frontend compiler to generate HiRes array output types.
      */
    def regenerateFromInputs(arrayGenerator: OutputArrayGenerator): Unit = {
      val arrayInputs = inputs.map(_.output)
      val (o, a) = arrayGenerator.apply(op.typed, arrayInputs, nodeId)
      this.output = o
      this.allocations = a

    }
    /** Returns an empty pass-through node attached to the end of this one.
      *
      * Note that the caller must effectuate the insertion by setting `this.seenBy`
      */
    def passthrough(): HiDag = {
      val hiOp = hi.DagOp()
      val output = this.output.cloneRef()
      new HiDag(
        op =
          HiArrayOp(
            typed = hi.TypedHiResOp(hiOp, this.op.typed.funcType, Nil),
            materialInputs = List(false),
            arrayInputs = List(false),
            dataParallelOutput = true,
            streamingOutput = true,
            lastLevelLoop = false,
            skipElaboration = true
          ),
        inputs = List(this),
        output = output,
        allocations = Nil,
        seenBy = this.seenBy,
        internalDag = None,
        cursors = this.cursors)
    }
}

object HiDag {
  /** Uniquely identifies a loop-controlling array index */
  class Cursor {
    val id = Cursor.ids.newId("k")
    override def toString = id.toString
  }

  object Cursor {
    private val ids = new lo.TempIds("_cur_")
  }

  def apply(op: hi.TypedHiResOp, arrayGenerator: OutputArrayGenerator): HiDag = {
    val builder = new HiDagBuilder(arrayGenerator)
    val dag = builder.getDag(op)
    dag.fillBackwardEdges()
    dag
  }
}

/** Generic form of a transformation at the HiRes-array op level.
  *
  * This encompasses both sub-array and flat-array fusion, and eventually
  * maybe some others as well.
  */
trait HiDagTransform[T] {
  import HiDagTransform._

  /** Apply the transform by mutating the given `dag`. */
  def updateDag(dag: HiDag): T
}

object HiDagTransform {

  /** Modifies the HiDag by creating a `Cat` node of `bottom` `outputs` and replacing
    * all references to them with references to corresponding `Uncat` nodes.
    *
    * @note that `bottom` will be the head output, and it should not be in `outputs`.
    *
    * @returns the resulting `Cat` node, which is the output of the new sub-HiDag,
    *           and a map from previous outputs to their corresponding virtual nodes.
    */
  def catNodesAndMap(
      bottom: HiDag,
      outputs: List[HiDag],
      interior: Set[HiDag]): (HiDag, Map[HiDag, HiDag]) = {
    val newBottom = {
      val inputs = bottom :: outputs
      val hiOp =
        hi.Cat(
          head = hi.DagOp(bottom.nodeId),
          tail = outputs.map(o => hi.DagOp(o.nodeId)):_*)
      val funcType =
        hi.Func(
          from =
            inputs
              .map(_.op.typed.funcType.from)
              .foldLeft(Map[hi.Id, hi.Data]()) { _ ++ _ },
          to = bottom.op.typed.funcType.to)
      val outputArray =
        MultiArray(
          bottom.output.cloneRef(),
          outputs.map(_.output.cloneRef()):_*)
      val hiArrayOp =
        HiArrayOp(
          typed = hi.TypedHiResOp(hiOp, funcType, inputs.map(_.op.typed)),
          materialInputs = inputs.map(_ => false),
          arrayInputs = inputs.map(_ => false),
          dataParallelOutput = true,
          streamingOutput = true,
          skipElaboration = true)
      new HiDag(
        op = hiArrayOp,
        inputs = inputs,
        seenBy = Nil,
        allocations = Nil,
        output = outputArray,
        internalDag = None,
        cursors = bottom.cursors)
    }
    val bottomDagOp = hi.DagOp

    val virtual = for ((n, i) <- (bottom :: outputs).zipWithIndex) yield {
      val hiOp = hi.Uncat(bottomDagOp(), i)
      val outputArray = n.output.cloneRef()
      val funcType =
        hi.Func(
          from = newBottom.op.typed.funcType.from,
          to = n.op.typed.funcType.to)
      val hiArrayOp =
        HiArrayOp(
          typed = hi.TypedHiResOp(hiOp, funcType, List(newBottom.op.typed)),
          materialInputs = n.inputs.map(_ => false),
          arrayInputs = n.inputs.map(_ => false),
          dataParallelOutput = true,
          streamingOutput = true,
          skipElaboration = true)
      new HiDag(
        op = hiArrayOp,
        inputs = List(newBottom),
        seenBy = n.seenBy.filter(!interior.contains(_)),
        output = outputArray,
        allocations = Nil,
        internalDag = None,
        cursors = bottom.cursors)
    }

    val virtMap = (bottom :: outputs).zip(virtual).toMap
    for ((o, v) <- virtMap) {
      for (n <- o.seenBy) if (!interior.contains(n)) {
        n.inputs = n.inputs.map(x => virtMap.get(x).getOrElse(x))
      }
      o.seenBy = newBottom :: o.seenBy.filter(interior.contains(_))
    }
    newBottom.seenBy = virtual
    assert(newBottom.seenBy.nonEmpty)
    (newBottom, virtMap)
  }

  val debug = false

  def debugln(s: String) {
    if (debug)
      println(s)
  }
}

/** Constructs an [[OpDag]] of [[HiArrayOp]]s from an [[hi.Operator]]
  * expression.
  */
class HiDagBuilder(arrayGenerator: OutputArrayGenerator) {
  private object NodeId {

    private var next = 0

    def apply(): Integer = {
      next += 1
      next
    }
  }

  /** Main method to construct an `OpDag` from an `Operator` */
  def getDag(op: hi.TypedHiResOp, idMap: Map[hi.Id, HiDag]=Map()): HiDag = {
    op.o match {
      // Check for cached nodes in the special case of an IdOp
      case o: hi.IdOp if (idMap.contains(o.id)) => {
        idMap(o.id)
      }
      case o: hi.Let => {
        var local = Map[hi.Id, HiDag]()
        for ((a, typed) <- o.assigns.zip(op.children)) {
          local += (a.id -> getDag(typed, idMap ++ local))
        }
        getDag(op.children.last, idMap ++ local)
      }
      case _ => {
        val dagInputs = op.children.foldLeft(List[HiDag]()) {
          case (list, child) => {
            list :+ getDag(child, idMap)
          }
        }

        val arrayOp = getArrayOp(op, dagInputs)
        val nodeId = Some(NodeId())
        val (output, newBuffers) = arrayGenerator.apply(arrayOp.typed, dagInputs.map(_.output), nodeId)
        val node = new HiDag(arrayOp, dagInputs, output, newBuffers)
        node.nodeId = nodeId
        node.inputs.map(_.seenBy +:= node)
        node
      }
    }
  }

  private def getArrayOp(typedOp: hi.TypedHiResOp, inputs: List[HiDag]): HiArrayOp = {
    typedOp.o match {
      case o: hi.IdOp => {
        HiArrayOp(
          materialInputs = Nil,
          arrayInputs = Nil,
          typed         = typedOp)
      }

      case o: hi.Uncat => {
        val newOp = hi.Uncat(hi.DagOp(inputs.head.nodeId), o.n)
        HiArrayOp(
          materialInputs = List(false),
          arrayInputs = List(false),
          typed = typedOp.copy(o = newOp),
          dataParallelOutput = true,
          skipElaboration       = true,
          streamingOutput = true)
      }

      case o: hi.InsertionSort => {
        val newOp = o.copy(hi.DagOp(inputs.head.nodeId))
        HiArrayOp(
          materialInputs    = List(false),
          arrayInputs       = List(false),
          typed             = typedOp.copy(o = newOp))
      }

      case o: hi.Split => {
        val isPar = o.isInstanceOf[hi.SplitPar]
        val newOp = o match {
          case p: hi.SplitPar => p.copy(o = hi.DagOp(inputs(0).nodeId))
          case s: hi.SplitSeq => s.copy(o = hi.DagOp(inputs(0).nodeId))
        }
        HiArrayOp(
          materialInputs      = List(true),
          arrayInputs         = List(false),
          typed               = typedOp.copy(o = newOp),
          dataParallelOutput  = true,
          streamingOutput     = true,
          raisesNestingLevel  = true,
          arrayNestingChange  = 1,
          skipElaboration     = true,
          lastLevelLoop       = false)
      }

      case o: hi.Histogram => {
        val newOp = o.copy(keys = hi.DagOp(inputs(0).nodeId))
        HiArrayOp(
          materialInputs  = List(false),
          arrayInputs     = List(false),
          blockingOutput  = true,
          typed           = typedOp.copy(o = newOp))
      }

      case o: hi.Offsets => {
        val inPlace = {
          def help(t: hi.Data): Boolean = t match {
            case a: hi.Arr => help(a.t)
            case hi.Hist(_) => true
            case o => false
          }
          help(inputs.head.op.typed.funcType.to) || o.inPlace
        }
        val newOp = o.copy(hi.DagOp(inputs.head.nodeId), inPlace=inPlace)
        HiArrayOp(
          materialInputs    = List(true),
          arrayInputs       = List(false),
          blockingOutput    = true,
          typed             = typedOp.copy(o = newOp),
          nonFusable        = o.depth > 1 || !o.inPlace,
          lowersNestingLevel = true,
          raisesNestingLevel = true,
          isNestedReduction = false,
          isInternalReduction = !inPlace,
          skipLoopLevels    = o.depth,
          lastLevelLoop     = false)
      }

      case o: hi.LastArray => {
        val newOp = hi.LastArray(hi.DagOp(inputs.head.nodeId))
        HiArrayOp(
          materialInputs     = List(true),
          arrayInputs        = List(true),
          blockingOutput      = true,
          typed               = typedOp.copy(o = newOp),
          isNestedReduction   = true,
          skipLoopLevels      = 1,
          lastLevelLoop       = false)
      }

      case o: hi.RestoreHistogram => {
        val newOp = o.copy(
          values = hi.DagOp(inputs.head.nodeId),
          hist = hi.DagOp(inputs(1).nodeId))
        HiArrayOp(
          materialInputs      = List(false, true),
          arrayInputs         = List(false, false),
          blockingOutput      = true,
          typed               = typedOp.copy(o = newOp),
          raisesNestingLevel  = true,
          lastLevelLoop       = false)
      }

      case o: hi.HashTable => {
        val newOp = o.copy(hi.DagOp(inputs.head.nodeId), hash = o.hash.map(_ => hi.DagOp(inputs(1).nodeId)))
        HiArrayOp(
          materialInputs = List(false, false),
          arrayInputs = List(false, false),
          blockingOutput = true,
          controlsChunkCursor = true,
          raisesNestingLevel = true,
          typed = typedOp.copy(newOp)
        )
      }

      case o: hi.HashJoin => {
        val newOp = o.copy(
          hi.DagOp(inputs(0).nodeId),
          hi.DagOp(inputs(1).nodeId),
          hi.DagOp(inputs(2).nodeId))

        HiArrayOp(
          materialInputs = inputs.map(_ => false),
          arrayInputs = List(false, o.parallel, false),
          typed = typedOp.copy(o = newOp),
          controlsOutputCursor = true,
          controlsChunkCursor = true)
      }

      case o: hi.Partition => {
        val newOp = o.copy(
          keys    = hi.DagOp(inputs(0).nodeId),
          values  = hi.DagOp(inputs(1).nodeId),
          hist    = hi.DagOp(inputs(2).nodeId))

        HiArrayOp(
          materialInputs      = List(false, false, true),
          arrayInputs         = inputs.map(_ => false),
          streamingOutput     = false,
          typed               = typedOp.copy(o = newOp),
          arrayNestingChange  = 0,
          dynamicAllocation   = o.disjoint,
          blockingOutput      = true,
          dataParallelOutput  = false)
      }

      case o: hi.Flatten => {
        val newOp = hi.Flatten(hi.DagOp(inputs.head.nodeId))
        HiArrayOp(
          materialInputs      = List(false),
          arrayInputs         = List(false),
          typed               = typedOp.copy(o = newOp),
          lowersNestingLevel  = true,
          arrayNestingChange  = -1,
          dataParallelOutput  = true,
          skipElaboration     = true,
          streamingOutput     = true)
      }

      case o: hi.Compact => {
        val newOp = hi.Compact(hi.DagOp(inputs.head.nodeId), hist = o.hist.map(_ => hi.DagOp(inputs(1).nodeId)))
        val hashCompact = inputs.head.output match {
          case c: ChunkArray => true
          case _ => false
        }
        HiArrayOp(
          materialInputs      = inputs.map(_ => false),
          arrayInputs         = true :: inputs.tail.map(_ => false),
          dataParallelOutput  = !hashCompact,
          controlsOutputCursor = true,
          streamingOutput     = true,
          blockArrayFusion    = hashCompact,
          lowersNestingLevel  = hashCompact,
          raisesNestingLevel  = hashCompact,
          dynamicAllocation   = hashCompact,
          typed               = typedOp.copy(o = newOp))
      }

      case o: hi.Assign => inputs.head.op

      case o: hi.Mask => {
        val newOp = hi.Mask(o = hi.DagOp(inputs(0).nodeId), cond = hi.DagOp(inputs(1).nodeId))
        HiArrayOp(
          materialInputs        = List(false, false),
          arrayInputs           = List(false, false),
          streamingOutput       = true,
          dataParallelOutput    = true,
          typed                 = typedOp.copy(o = newOp))
      }

      case o: hi.Block => {
        val newOp = o.copy(o = hi.DagOp(inputs.head.nodeId))
        HiArrayOp(
          materialInputs        = List(false),
          arrayInputs           = List(o.nest),
          blockingOutput        = true,
          raisesNestingLevel    = o.nest,
          lowersNestingLevel    = o.nest,
          blockArrayFusion      = o.nest,
          nonFusable            = o.nonFusable,
          skipElaboration       = true,
          typed                 = typedOp.copy(o = newOp))
      }

      case o: hi.Collect => {
        val newOp = hi.Collect(o = hi.DagOp(inputs.head.nodeId))
        HiArrayOp(
          materialInputs        = List(false),
          arrayInputs           = List(false),
          streamingOutput       = false,
          dataParallelOutput    = false,
          controlsOutputCursor  = true,
          blockingOutput        = true,
          typed                 = typedOp.copy(o = newOp))
      }

      case o: hi.Eval => {
        val newOp = hi.Eval(hi.DagOp(inputs.head.nodeId), o.func)
        HiArrayOp(
          materialInputs      = inputs.map(_ => false),
          arrayInputs         = inputs.map(_ => false),
          typed               = typedOp.copy(o = newOp),
          dataParallelOutput  = true,
          streamingOutput     = true)
      }

      case o: hi.Hash64 => {
        val newOp = hi.Hash64(hi.DagOp(inputs.head.nodeId), o.bits)
        HiArrayOp(
          materialInputs      = inputs.map(_ => false),
          arrayInputs         = inputs.map(_ => false),
          typed               = typedOp.copy(o = newOp),
          dataParallelOutput  = true,
          streamingOutput     = true)
      }

      case o: hi.Position => {
        val newOp = o.copy(hi.DagOp(inputs.head.nodeId))
        HiArrayOp(
          materialInputs      = inputs.map(_ => false),
          arrayInputs         = inputs.map(_ => false),
          typed               = typedOp.copy(o = newOp),
          dataParallelOutput  = true,
          streamingOutput     = true)
      }

      case o: hi.Reduce => {
        val newOp = hi.Reduce(hi.DagOp(inputs.head.nodeId), o.op, o.init)
        HiArrayOp(
          materialInputs      = inputs.map(_ => false),
          arrayInputs         = inputs.map(_ => false),
          typed               = typedOp.copy(o = newOp),
          blockingOutput      = true,
          controlsOutputCursor= true)
      }

      case o: hi.NestedReduce => {
        val newOp = hi.NestedReduce(hi.DagOp(inputs.head.nodeId), o.op, o.init)
        HiArrayOp(
          materialInputs      = inputs.map(_ => false),
          arrayInputs         = inputs.map(_ => true),
          typed               = typedOp.copy(o = newOp),
          blockingOutput      = true,
          lowersNestingLevel  = true,
          isNestedReduction   = true,
          skipLoopLevels      = 1,
          lastLevelLoop       = false,
          controlsOutputCursor= true)
      }

      case o: hi.Zip => {
        val newOp = hi.Zip(inputs.map(o => hi.DagOp(o.nodeId)):_*)
        HiArrayOp(
          materialInputs     = inputs.map(_ => false),
          arrayInputs         = inputs.map(_ => false),
          typed               = typedOp.copy(o = newOp),
          dataParallelOutput  = true,
          streamingOutput     = true)
      }

      case o: hi.Project => {
        val newOp = hi.Project(inputs.map(o => hi.DagOp(o.nodeId)):_*)
        HiArrayOp(
          materialInputs     = inputs.map(_ => false),
          arrayInputs         = inputs.map(_ => false),
          typed               = typedOp.copy(o = newOp),
          dataParallelOutput  = true,
          streamingOutput     = true)
      }

      case o: hi.Gather => {
        val newOp = hi.Gather(hi.DagOp(inputs(0).nodeId), hi.DagOp(inputs(1).nodeId))
        HiArrayOp(
          materialInputs     = List(false, true),
          arrayInputs         = inputs.map(_ => false),
          typed               = typedOp.copy(o = newOp),
          dataParallelOutput  = true,
          streamingOutput     = true)
      }

      case o: hi.Cat => {
        val newOp = hi.Cat(hi.DagOp(inputs.head.nodeId), inputs.tail.map(o => hi.DagOp(o.nodeId)):_*)
        HiArrayOp(
          materialInputs = inputs.map(_ => false),
          arrayInputs = inputs.map(_ => false),
          typed = typedOp.copy(o = newOp),
          dataParallelOutput = true,
          skipElaboration = true,
          streamingOutput = true)
      }

      case o: hi.DagOp => ???
    }
  }
}
