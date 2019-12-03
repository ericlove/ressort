// See LICENSE.txt
/** hi-compiler: Compiles declarative HiRes expressions into LoRes programs
  * for use by the backend.
  */

package ressort.hi.compiler
import ressort.compiler._
import ressort.lo.compiler.SplitLoRes
import ressort.lo._
import ressort.hi
import ressort.lo.compiler.AstTransform
import scala.collection.mutable.{ArrayBuffer, HashMap, LinkedHashSet, HashSet}
import scala.collection.immutable.Map


/** HiRes Operator -> LoRes Compiler */
class HiResCompiler(
    implicit val config: CompilerConfig=CompilerConfig.DefaultConfig) {
  import HiResCompiler._

  /** Compile the given [[hi.Operator]] into LoRes code and return
    * a certification of this result.
    */
  def compile(
      hiOp: hi.Operator,
      funcType: hi.Func,
      verbose: Boolean=false,
      name: Option[String]=None): CompiledLoRes = {

    val compilation = new HiResCompilation(config, hiOp, funcType, verbose, name)
    val finalLo = compilation.compile()
    finalLo
  }
}

class HiResCompilation(
      val config: CompilerConfig,
      val hiOp: hi.Operator,
      val funcType: hi.Func,
      val verbose: Boolean,
      val name: Option[String]=None) {

  import HiResCompiler._
  val tempIds = new TempIds("r_")

  val arrayGenerator = new OutputArrayGenerator(funcType, config)

  def compile(): CompiledLoRes = {
    // Checks if the input operator is type-safe, throws exception if not
    val typedHiResOp = hi.TypedHiResOp(hiOp)(funcType.from)
    val inferredFuncType = typedHiResOp.funcType
    if (!funcType.to.accepts(inferredFuncType.to)) {
      val err = {
        s"Operator output type incompatible with funcation declaration:\n"+
        s"Declared output type:\n${funcType.to}\n" +
        s"Actual type:\n${inferredFuncType.to}\n"
      }
      throw new Error(err)
    }
    val scheduledDag = getScheduledDag(typedHiResOp)

    val funcDec = {
      val func = compiledFunc(hiOp, funcType, scheduledDag)
      func.copy(name = name.map(Id) getOrElse func.name)
    }
    CompiledLoRes(hiOp, funcType, funcDec, Block(Nil))
  }

  /** Runs main phases of compilation and returns a scheduled Dag and
    * prints optional debugging information if `verbose` is set.
    */
  def getScheduledDag(hiOp: hi.TypedHiResOp) = {
    if (verbose) {
      println("\nCompiling Function:")
      println(hiOp)
      println("")
    }

    val initialDag = HiDag(hiOp, this)
    if (verbose) {
      println("######## INITIAL Dag PHASE ########")
      initialDag.print()
      println("################################\n\n")
    }

    val fusedDag = {
      val xthru = initialDag.passthrough()
      initialDag.seenBy = List(xthru)
      var newDag = xthru
      for (t <- dagTransforms) {
        newDag = t.updateDag(newDag)
      }
      newDag
    }

    if (verbose && (config.arrayFusion || config.vectorFusion)) {
      println("########### FUSED Dag ############")
      fusedDag.print()
      println("################################\n\n")
    }

    val loArrayDag = LoDag(fusedDag, tempIds)
    if (verbose) {
      println("######## ALLOCATION PHASE #########")
      loArrayDag.print()
      println("################################\n\n")
    }

    val elaboratedDag = ElaboratedDag(loArrayDag, config)
    val scheduledDag = scheduleDag(elaboratedDag)

    scheduledDag
  }

  private val dagTransforms: List[HiDagTransform[HiDag]] = {
    def check(cond: Boolean)(trans: OutputArrayGenerator => HiDagTransform[HiDag]) = {
      if (cond) Some(trans(arrayGenerator)) else None
    }
    val shellNodeInsertion = new InsertShellNodes()
    val arrayFusion = check(config.arrayFusion) (new ArrayFuser(_))
    val vectorFusion = check(config.vectorFusion) (new VectorFuser(_))
    List(
      Some(shellNodeInsertion),
      arrayFusion,
      vectorFusion).flatten
  }

  /** Returns a linear ordering of all nodes in an elaborated Dag */
  private def scheduleDag(elaboratedDag: ElaboratedDag): List[ElaboratedDag] = {
    val visited = HashSet[ElaboratedDag]()

    // The default schedule is just a depth-first traversal of the dag;
    // future versions of the compiler will generate more sophisticated plans.
    def traverse(dag: ElaboratedDag): List[ElaboratedDag] = {
      val inputs = (dag.inputs.map(traverse(_)).flatten)
      if (visited.contains(dag)) {
        inputs
      } else {
        visited += dag
        inputs ++ List(dag)
      }
    }

    traverse(elaboratedDag)
  }


  /** Removes any [[Free]]s from `deallocation` that reference an LValue whose root is in `returned` */
  private def removeReturnedFrees(deallocation: LoAst, returned: ArrayView): LoAst = {
    val rset = returned.array.buffers.map(_.name).toSet
    def trans(ast: LoAst): LoAst = {
      val newCh = ast.replaceAstChildren(ast.astChildren.map(trans))
      newCh match {
        case Free(l) if rset.contains(l.root) => Nop
        case other => other
      }
    }
    trans(deallocation)
  }

  /** Returns a schedule of allocations for the given DAG `schedule`
    *
    * Some allocations can be scheduled statically, while others require run-time determination of
    * array lengths known only after a specific node's execution. This pass moves static allocations
    * to the first node in the schedule, while others are placed after their last dependency.
    */
  private def scheduleAllocs(schedule: List[ElaboratedDag]): Array[LoAst] = {
    /** For each node in the `schedule`, a set of [[SymLike]] ids on which its allocation depends,
      * and which it produces.
      */
    val setList = {
      for (edag <- schedule) yield {
        var deps = Set[SymLike]()
        var prods = Set[SymLike]()
        def walk(ast: LoAst): Unit = {
          def walkExpr(e: Expr): Unit = {
            e.children.map(walkExpr)
            e match {
              case s: SymLike => deps += s
              case _ =>
            }
          }
          ast.astChildren.map(walk)
          ast match {
            case a: AssignLike => prods += a.lhs.root
            case h: HeapAlloc => h.length.map(walkExpr)
            case _ =>
          }
        }
        walk(edag.op.loop.allocation)
        (deps, prods)
      }
    }

    /** Set of values in at least one products list */
    val allProducts = {
      var s = Set[SymLike]()
      setList.map(s ++= _._2)
      s
    }

    /** The index of the node that produces each dependency */
    val producingNode = {
      var m = Map[SymLike, Int]()
      for (((deps, prods), i) <- setList.zipWithIndex) {
        prods.map(p => m = m + (p -> i))
      }
      m
    }

    val allocations = Array.fill[LoAst](schedule.length)(Nop)

    for ((edag, (deps, prods)) <- schedule.zip(setList)) {
      val depNodes = deps.filter(allProducts.contains).map(producingNode)
      val maxDep = if (depNodes.nonEmpty) depNodes.max else 0
      allocations(maxDep) += edag.op.loop.allocation
    }

    allocations
  }

  /** Returns an LoRes [[FuncDec]] for a compiled operator with the proper
    * arugment names and return type.
    */
  private def compiledFunc(hiOp: hi.Operator, funcType: hi.Func, dag: ScheduledDag): FuncDec = {
    val funcName = Id(transOpNameStr(hiOp))
    val finalizer = {
      removeReturnedFrees(Block(dag.map(_.op.loop.deallocation)), dag.last.output)
    }
    val allocs = scheduleAllocs(dag)
    val body =
      Block(
        dag.zip(allocs).map(x =>
          x._2 + // alloc
          x._1.op.loop.higherInit +
          x._1.op.loop.initializer +
          x._1.op.loop.body).toList)
    val inputs = getLoInputs(hiOp, funcType)
    val (returnStmt, outType) = getReturn(dag)

    val op = {
      FuncDec(
        funcName,
        inputs, 
        {
          body +
          finalizer +
          returnStmt
        },
        Some(outType))
    }

    op
  }

  /** Returns an LoRes [[Return]] statement for the end of a compiled function,
    * along with its `LoType`
    */
  private def getReturn(dag: ScheduledDag): (LoAst, Primitive) = {
      val struct = dag.last.output.array.struct
      val tmpVar = tempIds.newId("out_wrap")
      val returnStmt = {
        Dec(tmpVar, Ptr(struct)) +
        HeapAlloc(tmpVar) +
        dag.last.output.array.assignToStruct(Deref(tmpVar)) +
        Return(tmpVar)
      }
      val outType = Ptr(struct)
      (returnStmt, outType)
  }



  /** Returns a typed map of all LoRes inputs to the compiled op function */
  private def getLoInputs(hiOp: hi.Operator, funcType: hi.Func): Seq[(Id, Primitive)] = {
    val inputsHiRes = funcType.from
    val inputsLo = inputsHiRes map {
      case (a,b) => {
        b match {
          case st: hi.Primitive => {
            Map(Id(a.name) -> LoType(st).toPrimitive)
          }
          case other => {
            Map(Id(a.name) -> Ptr(LoType(other)))
          }
        }
      }
    }
    inputsLo.foldLeft(List[(Id, Primitive)]()) { _ ++ _ }
  }
}

object HiResCompiler {
  /** A schedule is a list of Dag nodes in order their LoRes code and 
    * allocations should appear.
    */
  type ScheduledDag = List[ElaboratedDag]
  
  /** An HiRes `Operator` paired with its compiled LoRes code. */

  case class CompiledLoRes(
      hiOp:  hi.Operator,
      hiType: hi.Func,
      func: FuncDec,
      defs: Block)

  def transOpNameStr(hiOp: hi.Operator): String = {
    def transJoinName(outer: hi.Operator, inner: hi.Operator): String = {
      transOpNameStr(outer) + "J_" + transOpNameStr(inner)
    }
    hiOp match {
      case hi.IdOp(_)                       => "Rel"
      case hi.InsertionSort(o, _)           => "InsSrt_"+transOpNameStr(o)
      case hi.MergeSort(o)                  => "MrgSrt_"+transOpNameStr(o)
      case mr: hi.Partition                 => "MvRecsH_"+transOpNameStr(mr.values)
      case bh: hi.Histogram                 => "BuildHist_"+transOpNameStr(bh.keys)
      case hi.Offsets(o, _, _, _)           => "RdceHist_"+transOpNameStr(o)
      case hi.RestoreHistogram(o, _, _)     => "RstHist_"+transOpNameStr(o)
      case hi.LastArray(o)                  => "MrgHist_"+transOpNameStr(o)
      case hi.Eval(o, _)                    => transOpNameStr(o)
      case hi.Flatten(o)                    => transOpNameStr(o)
      case hi.SplitSeq(o, _, _, _)          => "SplitSeq_"+transOpNameStr(o)
      case hi.SplitPar(o, _, _, _)          => "SplitPar_"+transOpNameStr(o)
      case hi.Mask(value, _)                => "Mask"+transOpNameStr(value)
      case hi.Collect(o)                    => "Collect_"+transOpNameStr(o)
      case hi.Assign(id, _)                 => "Assign "+id
      case hi.Compact(o, _, _)              => transOpNameStr(o)
      case hi.Reduce(o, op, init)           => "Reduce_"+transOpNameStr(o)
      case hi.NestedReduce(o, op, init)     => "NestedReduce_"+transOpNameStr(o)
      case hi.Position(o, _)                => "Pos_"+transOpNameStr(o)
      case hi.Let(_, o)                     => transOpNameStr(o)
      case z: hi.Zip                        => {
        val subStrs = z.ops map transOpNameStr
        subStrs.foldLeft("Zip") { case (s1, s2) => s"${s1}_$s2" }
      }
      case p: hi.Project => {
        val subStrs = p.ops map transOpNameStr
        subStrs.foldLeft("Proj") { case (s1, s2) => s"${s1}_$s2" }
      }
      case b: hi.Block => "Block_"+transOpNameStr(b.o)
      case h: hi.Hash64 => "Hash64_"+transOpNameStr(h.o)
      case other => throw new Error("Unknown operator type "+other)
    }
  }

  def transOpName(hiOp: hi.Operator): Id = Id(transOpNameStr(hiOp))
}
