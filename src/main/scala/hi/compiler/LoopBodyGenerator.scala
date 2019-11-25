// See LICENSE.txt
package ressort.hi.compiler
import ressort.compiler._
import ressort.lo
import ressort.hi._

/** Generates the innermost loop of execution for `op`. 
  *
  * This is the central dispatch for all code generator classes.
  * Its output is the body of the loop around which the
  * [[LoopNestGenerator]] adds additional layers in accordance with the given
  * array views.
  */
class LoopBodyGenerator(elaboration: Elaboration, node: LoDag) {
  private val inputs: List[ArrayView] = node.inputViews
  private val output: ArrayView = node.outputView
  private val op: Operator = node.op.op

  lazy val cursor = inputs.head.vectorCursor.getOrElse(lo.Const(0))

  private val tempIds = elaboration.tempIds

  lazy val innerLoop: LoopLevel = op match {
    case o: IdOp => LoopLevel(lo.Nop)

    case o: InsertionSort => {
      val gen = InsertionSortGenerator(elaboration)
      LoopLevel(gen.emit(inputs, output, o))
    }

    case o: Histogram => {
      val gen = BuildHistogramGenerator(elaboration)
      LoopLevel(
        gen.emit(
          inputs.head,
          output,
          cursor,
          o))
    }

    case o: Partition => {
      val gen = PartitionGenerator(elaboration)
      val keys = inputs(0)
      val values = inputs(1)
      val hist = inputs(2)
      val output = this.output.asInstanceOf[MultiArray.View]
      val outBuf = output.head
      val (swwcb, swwcbHist) = {
        if (elaboration.config.rpart.useWriteBuffer) {
          (Some(output.tail(1)), Some(output.tail(2)))
        } else {
          (None, None)
        }
      }
      val loop = gen.emit(
        keys = keys,
        values = values,
        hist = hist,
        output = outBuf,
        cursor = cursor,
        swwcb = swwcb,
        swwcbHist = swwcbHist,
        op = o)
      loop.copy(body = mask(inputs.head, loop.body))
    }

    case o: Offsets => {
      val gen = OffsetsGenerator(elaboration)
      val hist = output
      val res = gen.emit(inputs.head.asInstanceOf[ArrayView with ParallelMacroView], hist, o)
      res
    }

    case o: LastArray => {
      val gen = LastArrayGenerator(elaboration)
      LoopLevel(
        gen.emit(
          inputs,
          output,
          o))
    }

    case o: RestoreHistogram => {
      val gen = RestoreHistogramGenerator(elaboration)
      val ast = output match {
        case d: DisjointArray.View => lo.Nop
        case _ => gen.emit(inputs, output, o)
      }
      LoopLevel(ast)
    }

    case o: SplitSeq => LoopLevel(lo.Nop)

    case o: SplitPar => LoopLevel(lo.Nop)

    case o: Flatten => LoopLevel(lo.Nop)

    case DagOp(_) => {
      // Note that internal Dags will be elaborated separately by the caller
      LoopLevel(lo.Nop)
    }

    case o: Compact => {
      val outCursor = output.vectorCursor.getOrElse(tempIds.newId("cpcur"))
      val gen = CompactGenerator(elaboration)
      val alloc = {
        // Since `Compact` is dynamically allocated, we know that a symbol will have
        // been designated to contain its output's length.
        val lenVar = output.array.buffer.length.asInstanceOf[lo.SymLike]
        o.hist match {
          case None => lo.DecAssign(lenVar, lo.Index(), inputs.head.array.buffer.length)
          case Some(_) => {
            val harr = inputs(1)
            // Generate all code needed to set the histogram to the last sub-array
            // at all levels and extract it's final entry, which should give the total length.
            val setEndState: lo.LoAst = {
              def walk(v: ArrayView): lo.LoAst = {
                v match {
                  case n: NestedView => walk(n.base) + n.globalState + n.endLocalState
                  case _ => v.globalState + v.endLocalState
                }
              }
              walk(harr)
            }
            val max = harr.access(harr.maxCursor-lo.Const(1))
            // Wrap in an `If(true)` to avoid any namespace collisions.
            lo.Dec(lenVar, lo.Index()) +
            lo.If(lo.True, setEndState + lo.Assign(lenVar, max))
          }
        }
      }

      val head = new RecParallelIO(inputs.head, cursor)
      LoopLevel(
        gen.emit(head, output, outCursor, o), allocation = alloc)
    }

    case o: Mask => {
      val gen = MaskGenerator(elaboration)
      LoopLevel(
        gen.emit(
          values = new RecParallelIO(inputs(0), cursor),
          cond = new RecParallelIO(inputs(1), cursor),
          output = new RecParallelIO(output, cursor),
          o))
    }

    case o: Block => LoopLevel(lo.Nop)

    case o: Collect => {
      val gen = CollectGenerator(elaboration)
      // Output vectorCursor should be specially allocated in [[LoDag]]
      val outCursor = output.vectorCursor.get
      val main = gen.emit(
        new RecParallelIO(inputs.head, cursor),
        new StreamingIO(this.output, outCursor),
        o)
      LoopLevel(main)
    }

    case o: Reduce => {
      val gen = ReduceGenerator(elaboration)
      val outCursor = output.vectorCursor.getOrElse(lo.Const(0))
      val innerLoop =
        gen.emit(
          input = new RecParallelIO(inputs.head, cursor),
          output = new RecParallelIO(output, outCursor),
          nested = false,
          o)
      val body = mask(inputs.head, innerLoop.body)
      
      innerLoop.copy(body = 
        body,
        initializer = innerLoop.initializer )
    }

    case o: Position => {
      val code = {
        mask(
          inputs.head,
          output.access(cursor) := (if (o.relative) cursor else output.offset + cursor))
      }
      LoopLevel(code)
    }

    case o: Hash64 => {
      val gen = new Hash64Generator(elaboration)
      val code = {
        mask(
          inputs.head,
          gen.emit(
            new RecParallelIO(inputs.head, cursor),
            new RecParallelIO(this.output, cursor),
            o)
          )
      }
      LoopLevel(code)
    }

    case o: NestedReduce => {
      // We can reuse the existing generator for Reduce, so long as we generate
      // a different set of loops around it.
      val gen = ReduceGenerator(elaboration)
      val initVar = tempIds.newId("init")
      val leader = inputs.head
      val vecCursor = output.vectorCursor.getOrElse(tempIds.newId("vcur"))
      val arrCursor = leader.cursor.getOrElse(tempIds.newId("acur"))
      val vmax = tempIds.newId("vmax")

      val innerLoop = 
        gen.emit(
          input = new RecParallelIO(inputs.head, vecCursor),
          output = new RecParallelIO(output, vecCursor),
          nested = true,
          Reduce(o.o, o.op, o.init))
      val body = mask(inputs.head, 
        innerLoop.body)

      val code = {
        elaboration.states.globalState(arrCursor) +
        elaboration.states.resetLocalState(arrCursor) +
        lo.DecAssign(vmax, lo.Index(true), output.maxCursor) +
        innerLoop.initializer +
        inputs.head.resetLocalState +
        lo.ForBlock(vecCursor, vmax,
          inputs.head.getLocalState(vecCursor) +
          o.init.map(i => (output.access(vecCursor) := lo.Expr(i))).getOrElse(lo.Nop) +
          lo.ForBlock(arrCursor, leader.numArrays,
            elaboration.states.localState(arrCursor) +
            elaboration.states.resetLocalState(arrCursor) +
            body) +
          inputs.head.getIncrementLocalState)
      }

      LoopLevel(body = code)
    }

    case o: Eval => {
      val gen = EvalGenerator(elaboration)
      val code = {
        mask(
          inputs.head,
          gen.emit(
            new RecParallelIO(inputs.head, cursor),
            new RecParallelIO(this.output, cursor),
            o))
      }
      LoopLevel(code)
    }

    case o: Zip => {
      val gen = ZipProjectGenerator(elaboration)
      LoopLevel(
        mask(
          inputs.head,
          gen.emit(
            inputs map { i => new RecParallelIO(i, cursor) },
            new RecParallelIO(output, cursor),
            o)))
    }

    case o: Project => {
      val gen = ZipProjectGenerator(elaboration)
      LoopLevel(
        mask(
          inputs.head,
          gen.emit(
            inputs map { i => new RecParallelIO(i, cursor) },
            new RecParallelIO(output, cursor),
            o)))
    }

    case o: Gather => {
      val gen = GatherGenerator(elaboration)
      val code = {
        mask(
          inputs(0),
          gen.emit(
            indices = new RecParallelIO(inputs(0), cursor),
            target = inputs(1),
            output = new RecParallelIO(output, cursor),
            op = o))
      }
      LoopLevel(code)
    }

    case o: Cat =>  LoopLevel(lo.Nop)

    case o: Uncat => LoopLevel(lo.Nop)

    case o: HashTable => {
      val gen = HashTableGenerator(elaboration)
      LoopLevel(
        mask(
          inputs(0),
          gen.emit(
            new RecParallelIO(inputs(0), cursor),
            o.hash.map(_ => new RecParallelIO(inputs(1), cursor)),
            output.asInstanceOf[ArrayView with ParallelMacroView],
            o)
        )
      )
    }

    case o: HashJoin => {
      val gen = HashJoinGenerator(elaboration)
      val chunkArray = output.asInstanceOf[ChunkArray.ChunkView]
      val chunkCursor = chunkArray.cursor.get
      val init = {
        var i: lo.LoAst = lo.Nop
        if (node.op.raisesNestingLevel) {
          i += chunkArray.base.globalState + chunkArray.base.resetLocalState
        }
        i += elaboration.states.globalState(chunkCursor)
        i += elaboration.states.resetLocalState(chunkCursor)
        i
      }

      def builder(ast: lo.LoAst): lo.LoAst = {
        val innerBuilder = 
          gen.emit(
              new RecParallelIO(inputs(0), cursor),
              inputs(1).asInstanceOf[NestedView with ParallelMacroView],
              new RecParallelIO(inputs(2), cursor),
              chunkArray,
              o)
        val res = mask(inputs(0), innerBuilder(ast))
        res
      }

      LoopLevel(
         initializer = init,
         body = builder(lo.Nop),
         builder = Some(builder(_))
       )
    }
  }

  private def mask(leader: ArrayView, body: lo.LoAst): lo.LoAst = {
    leader.readMask(cursor) match {
      case Some(m) => lo.If(m, body)
      case None => body
    }
  }

}
