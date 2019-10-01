package ressort.hi.compiler

import ressort.lo._
import ressort.hi
import scala.collection.mutable.{LinkedHashSet, HashMap, HashSet}
import scala.collection.mutable



/** A HiRes operator DAG whose inputs and outputs have allocated arrays with views. */
class LoDag(
    val op          : HiArrayOp,
    val inputs      : List[LoDag],
    val inputViews  : List[ArrayView],
    val output      : MetaArray,
    val outputView  : ArrayView,
    val tempIds     : TempIds,
    val internalDag : Option[LoDag] = None,
    val allocation  : LoAst=Nop,
    val deallocation: LoAst=Nop,
    val localAlloc  : LoAst=Nop,
    val ownCursors  : Set[SymLike]=Set())
  extends OpDag[MetaArray, HiArrayOp, LoDag]

object LoDag {
  def apply(hiDag: HiDag, tempIds: TempIds): LoDag = {
    val trans = new LoDagBuilder(tempIds)
    trans.loArrayDag(hiDag)
  }

}

/** Converts `HiArray` DAGs into [[ArrayView]] DAGs and allocates them */
class LoDagBuilder(tempIds: TempIds) {
  def loArrayDag(node: HiDag): LoDag = {
    if (nodeCache.contains(node)) {
      return nodeCache(node)
    } else if (node.inputs.nonEmpty) {
      // Pre-populate the cache with all prior nodes
      node.inputs.map(loArrayDag)
    }

    // All inputs should have had LoDag nodes made already
    val inputs = node.inputs.map(nodeCache)

    // (SymLke) Cursors for each nesting depth
    var cursors = Map[Int, SymLike](-1 -> cursorSyms(chunkCursor))

    // Cursors owned by this node
    var ownCursors = Set[SymLike]()

    // Cursors that were not bound by any [[HiDag]] node's `cursors` map (so created here)
    val newCursors = HashSet[HiDag.Cursor]()

    // Assign cursor symbols for every depth of this node's loop nest
    val depth = (node.output :: node.inputs.map(_.output)).map(_.depth).max
    for (i <- 0 to depth) {
      val cur: HiDag.Cursor = if (node.cursors.contains(i)) {
        node.cursors(i)
      } else {
        val c = new HiDag.Cursor()
        newCursors += c
        c
      }
      val sym = if (cursorSyms.contains(cur)) {
        cursorSyms(cur)
      } else {
        val s = tempIds.newId("fcur")
        cursorSyms += (cur -> s)
        s
      }
      cursors += (i -> sym)
    }
    ownCursors ++= node.ownCursors.flatMap(cursorSyms.get)
    if (node.internalDag.isEmpty)
      ownCursors ++= newCursors.map(cursorSyms)

    // Does this node control the shared "chunk cursor" in a given array?
    def ownsChunkCursor(a: MetaArray): Boolean = {
      // A node owns the chunk cursor iff it either:
      //    (b.) owns the level just __above__ the ChunkArray
      // or (a.) owns the ChunkArray AND the vector cursor
      // or (c.) owns the vector cursor when the ChunkArray is on top
      //
      // The reason for this is somewhat complicated: we want to allow "chaining" of chunk-
      // inducing operators inside one fused segment, where each chain link only disrupts
      // the level below chunking (e.g. vectors, unless the chunks themselves are sliced).
      var owned = false
      var ownsChunk = false
      var chunkOnTop = a match {
        case ch: ChunkArray => true
        case _ => false
      }
      def walk(a: MetaArray): Unit = {
        def owns(a: MetaArray): Boolean = {
          cursors.contains(a.depth) && ownCursors.contains(cursors(a.depth))
        }
        a match {
          case ch: ChunkArray if owns(ch) => {
            ownsChunk = true
            walk(ch.base)
          }
          case n: NestedArray => n.base match {
            case ch: ChunkArray => 
              if (owns(ch)) {
                owned = true
                ownsChunk = true
              } else {
                walk(ch.base)
              }
            case _ => walk(n.base)
          }
          case f: FlatArray if (owns(f) && ownsChunk) => owned = true
          case f: FlatArray if (owns(f) && chunkOnTop) => owned = true
          case _ =>
        }
      }
      walk(a)
      owned
    }
    val ownedChunkCursor = inputs.length > 0 && ownsChunkCursor(inputs.head.output)

    if (ownedChunkCursor) {
      nextChunkCursor()
      cursors += (-1 -> cursorSyms(chunkCursor))
      ownCursors += cursorSyms(chunkCursor)
    }

    // Assign views to each array and determine which cursors this node owns
    val inputViews = for ((i, n) <- inputs.zipWithIndex) yield {
      val origChunkCursor = chunkCursor
      val origChunkSym = cursorSyms(chunkCursor)

      val isArray = node.op.hiOp.isInstanceOf[hi.HashJoin] && (n == 1)
      if (isArray) {
        // Operators that control an array input need to generate a temporary
        // chunk cursor, so that the array input's view state is not controlled
        // by the main chunk cursor, if any exists.
        val fakeChunkSym = tempIds.newId("fake_chunk")
        val fakeChunkCur = new HiDag.Cursor()
        cursors += (-1 -> fakeChunkSym)
        ownCursors += (fakeChunkSym)
        chunkCursor = fakeChunkCur
      }

      val view = i.output.view(cursors, isOutput=false)

      if (isArray) {
        cursors += (-1 -> origChunkSym)
        chunkCursor = origChunkCursor
      }

      view
    }

    val outputView: ArrayView = {
      var outputCursors = Map[Int, SymLike]() ++ cursors
      // Make sure to create a new cursor for the output's bottom if this is a cursor-controlling node
      if (node.op.controlsOutputCursor) {
        val cur = node.cursors.getOrElse(0, new HiDag.Cursor())
        val sym = tempIds.newId("ocur")
        cursorSyms += (cur -> sym)
        newCursors += cur
        ownCursors += sym
        outputCursors += (0 -> sym)
      }

      // If this node controls the chunk cursor, create a special one just for its output
      if (node.op.controlsChunkCursor) {
        val cur = new HiDag.Cursor()
        val sym = tempIds.newId("ccur")
        chunkCursor = cur
        cursorSyms += (cur -> sym)
        newCursors += cur
        ownCursors += sym
        outputCursors += (-1 -> sym)
      }

      node.output.view(outputCursors, isOutput=true)
    }


    // Create a new LoDag node with new views for each input/output
    val loDag =
      new LoDag(
        op = node.op,
        inputs = inputs,
        inputViews = inputViews,
        output = node.output,
        outputView = outputView,
        tempIds = tempIds,
        internalDag = node.internalDag.map(loArrayDag),
        allocation = Block(node.allocations.map(_.constructor).toList),
        deallocation = Block(node.allocations.map(_.destructor).toList),
        localAlloc = Block(node.allocations.map(_.declareImmaterial).toList),
        ownCursors = ownCursors
      )

    if (ownedChunkCursor)
      nextChunkCursor()

    nodeCache(node) = loDag
    loDag
  }

  /** All [[HiDag]] nodes for which a [[LoDag]] has previously been produced */
  private val nodeCache = HashMap[HiDag, LoDag]()

  /** Actual LoRes symbols for each abstract cursor in the [[HiDag]] */
  private val cursorSyms = HashMap[HiDag.Cursor, SymLike]()

  /** Buffers whose allocation has already been assigned to a [[LoDag]] node */
  private val allocated = HashSet[Buffer]()

  /** Buffers whose deallocation has already been assigned to a [[LoDag]] node */
  private val deallocated = HashSet[Buffer]()

  /** Common cursor to be used on multi-input nodes for traversing chunk arrays
    *
    * The `chunkCursor` must be updated every time a chunk-controlling node is encountered,
    * so that the next chunk-controlling node's chunk cusor will not cause state updates for
    * array views from the previous chunk-controller.
    */
  private var chunkCursor: HiDag.Cursor = null
  private def nextChunkCursor(): Unit = {
    chunkCursor = new HiDag.Cursor()
    cursorSyms(chunkCursor) = tempIds.newId("ch_cur")
  }
  nextChunkCursor()

  private def allocate(b: Buffer): LoAst = {
    if (allocated.contains(b)) {
      Nop
    } else {
      allocated += b
      b.constructor
    }
  }

  private def deallocate(b: Buffer): LoAst = {
    if (deallocated.contains(b)) {
      Nop
    } else {
      deallocated += b
      b.destructor
    }
  }
}
