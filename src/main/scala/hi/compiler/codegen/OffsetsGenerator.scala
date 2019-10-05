// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi
import ressort.lo._
import ressort.hi.compiler._
import ressort.compiler._

/** Generates LoRes code for the [[hi.Offsets]] operator */
case class OffsetsGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "ReduceHistograms"

  def emit(
      input: ArrayView with ParallelMacroView,
      hist: ArrayView,
      op: hi.Offsets): LoopLevel = {
    val rhpi = {
      new OffsetsProblemInstance(
        input = input,
        hist = hist,
        op = op,
        generator = this)
    }

    rhpi.reduce
    
  }
}

class OffsetsProblemInstance(
    val input:   ArrayView with ParallelMacroView,
    val hist:       ArrayView,
    val op:         hi.Offsets,
    val generator:  OffsetsGenerator)
  extends HistogramOperatorInstance {
  
  // Parameters to HistogramOperatorInstance
  val elaboration = generator.elaboration 

  val (offs: ArrayView, sizes: Option[ArrayView]) = hist match {
    case m: MultiArray.View => (m.head, Some(m.tail.head))
    case _ => (hist, None)
  }

  /** [[ArrayView]] levels whose histograms' partitions will be merged */
  private val (mergeLevelsIn, meregeLevelsOut) = {
    def merge(view: ArrayView, depth: Int): List[ArrayView] = {
      if (depth > 0)
        view :: merge(view.asInstanceOf[NestedView].base, depth-1)
      else 
        view :: Nil
    }
    (merge(input, op.depth), merge(offs, op.depth))
  }

  private def sliceLength(slice: Expr): Expr = {
    input match {
      // ChunkArray requires a hack, because there is one extra inner loop
      // over each of the chunks in the chunk list, so can't use `maxCursor`
      // directly, as it will only equal the chunk size, not the total outer array length.
      case c: ChunkArray.ChunkView => c.state.count
      case _ if op.inPlace => input.accessExpr(slice)
      case _ => input.maxCursor
    }
  }

  def reduce: LoopLevel = {
    val ins = mergeLevelsIn.toArray
    val outs = meregeLevelsOut.toArray
    val cursors = ins.map(_ => elaboration.tempIds.newId("i"))
    val tmp = elaboration.tempIds.newId("tmp")
    val acc = elaboration.tempIds.newId("acc")

    // # of partitions: the last input view is the innermost (vector) level,
    // so it defines the number of partitions in each histogram.
    val numParts = offs.maxCursor-1 // (same as ins.last.maxCursor)

    // The last cursor is the vector cursor, which is also the partition index
    val part = cursors.last

    // In a normal reduction, the accumulator is global, so all arrays will have
    // offsets in a single, contiguous output buffer; in a disjoint reduction, the
    // accumulator is reset to zero for each separate buffer.
    val alloc = 
      DecAssign(tmp, Index(), 0) +
      DecAssign(acc, Index(), 0)

    def localState(view: ArrayView, cursor: SymLike): LoAst = view match {
      case p: NestedView with ParallelView => p.localState(cursor)
      case s: NestedView with SequentialView => s.incrementLocalState
      case _ => Nop
    }

    // AST result to be built up
    var ast: LoAst = Nop

    // Add the innermost loop body to the ast
    ast +=
        (if (!op.inPlace) input.macroState(part) else Nop) +
        (tmp := sliceLength(part)) +
        //Printf("Offsets %d (off %d) = %d", part, input.offset, acc) +
        (offs.access(part) := acc) +
        (acc := acc + tmp) +
        // For N partitions, update the `N+1`th counter, which sets the length of the Nth
        If(Equal(part, numParts-1),
          //Printf("Offsets %d (off %d) = %d", part+1, input.offset, acc) +
          (offs.access(part+1) := acc))

    // Add an array loop for all views but the last, which is the vector level
    for (i <- ins.indices.dropRight(1)) {
      val cur = cursors(i)
      ast =
        ForBlock(cur, ins(i).numArrays,
          ins(i+1).globalState +
          outs(i+1).globalState +
          localState(ins(i), cur) + 
          localState(outs(i), cur) +
          ast)
    }

    if (op.disjoint) {
      ast = alloc + ast + (sizes.get.access(part) := acc)
    }

    // If we control any arrays (surrounding the partitions vector), then we need to
    // set the state for those outside of the outermost partition loop
    val outerState = {
      if (ins.length > 1 && op.depth > 0) {
        val insRev = ins.reverse
        val outsRev = outs.reverse
        insRev.tail.head.globalState +
        insRev.tail.head.resetLocalState +
        outsRev.tail.head.globalState +
        outsRev.tail.head.resetLocalState
      } else {
        Nop
      }
    }

    // Outermost loop: loop over all the partitions. This ensures all independent threads'
    // histograms are processed for each partition before moving to the next partition
    ast = outerState + ForBlock(part, numParts, ast)

    op.depth match {
      case _ if (op.disjoint) => LoopLevel(ast)
      case _ if (!op.inPlace) => LoopLevel(ast, allocation = alloc)
      case 0 => LoopLevel(alloc + ast)
      case 1 => LoopLevel(ast, initializer = alloc)
      case _ => LoopLevel(ast, allocation = alloc)
    }
  }

  def msb = None
  def lsb = None
}

