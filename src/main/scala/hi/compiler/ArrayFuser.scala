package ressort.hi.compiler
import ressort.hi
import scala.collection.mutable.{HashMap, LinkedHashSet}
import scala.collection.mutable


class ArrayFuser(arrayGen: OutputArrayGenerator) extends HiDagTransform[HiDag] {
  /** Performs fusion of ops with co-indexed arrays, and returns the new DAG */
  def updateDag(dag: HiDag): HiDag = {
    var fusionDepth = 1
    var (end, fusedDags) = updateInternal(dag, fusionDepth)

    // Attempt fusion from depth=1 to depth=..., until no new fused DAGs produced
    while (fusedDags.nonEmpty) {
      fusionDepth += 1
      end.depthFirst { n => n.regenerateFromInputs(arrayGen) }
      var next = Seq[HiDag]()
      for (d <- fusedDags) {
        val res = d.internalDag.map(updateInternal(_, fusionDepth))
        res.map(next ++= _._2)
      }
      fusedDags = next
    }
    end
  }

  /** Attempts fusion on the given (partial or internal) `dag` at stated depth.
    *
    * @returns A pair containing the output node of the input dag, in case modified,
    *           and a [[Seq]] of any resulting fused DAG nodes.
    */
  private def updateInternal(dag: HiDag, fusionDepth: Int=1): (HiDag, Seq[HiDag]) = {
    val end = balanceNesting(dag)
    val segmenter = new ArraySegmenter(end, fusionDepth)
    val cliques = segmenter.doSegmentation()
    val fusedDags = if (!cliques.isEmpty) {
      val fuser = new HiDagFuser(cliques, fusionDepth, false, arrayGen)
      fuser.updateDag(end)
    } else {
      Seq()
    }
    (end, fusedDags)
  }

  /** Adds fake flattening nodes to the end of this HiDag until depth is zero */
  private def balanceNesting(dag: HiDag): HiDag = {
    val depth = dag.output.depth
    var res = dag
    for (i <- 0 until depth) {
      val xthru = res.passthrough()
      res.seenBy = List(xthru)
      res = xthru
      res.op = res.op.copy(lowersNestingLevel = true)
    }
    res
  }
}


class ArraySegmenter(dag: HiDag, fusionDepth: Int) {
  import HiDagTransform._
  def doSegmentation(): Seq[HiClique] = {
    def out(dag: HiDag): hi.Operator = dag.op.hiOp match {
      case _ if dag.internalDag.nonEmpty => out(dag.internalDag.get)
      case d: hi.DagOp => out(dag.inputs.head)
      case c: hi.Cat => out(dag.inputs.head)
      case _ => dag.op.hiOp
    }
    debugln(s"BEGIN ARRAY FUSE (output ${out(dag)})")
    val clist = cliques
    debugln(s"ARRAY FUSION SEGMENT LIST (depth $fusionDepth):")
    for (s <- clist) {
      debugln(s"\t-- ${s.bottom.head.op.hiOp} to ${s.top.head.op.hiOp}")
    }
    debugln("--\n")
    cliques
  }


  private def debugln(s: String=""): Unit = {
    if (OpDag.debug)
      println(s)
  }

  private def mustBeExcluded(d: HiDag): Boolean = {
    val res =
          d.internalDag.nonEmpty  ||
          d.op.isNestedReduction ||
          d.op.hiOp.isInstanceOf[hi.Uncat] ||
          d.op.hiOp.isInstanceOf[hi.Cat] ||
          d.op.hiOp.isInstanceOf[hi.DagOp]
    res
  }

  private lazy val (flatteners, exclude) = {
    val depths = HashMap[HiDag, Int]()
    var flatteners = Set[HiDag]()
    var exclude = Set[HiDag]()

    dag.depthFirst(n => depths(n) = n.output.depth)
    val startingDepth = depths(dag.top.head)
    debugln(s"STARTING DEPTH $startingDepth fuse depth $fusionDepth")
    dag.breadthFirstReverse { n =>
      val delta = {
        // Note that all inputs should have the same depth, since balancing
        // nodes have been inserted.
        if (n.inputs.nonEmpty)
          n.output.depth - n.inputs.head.output.depth
        else
          0
      }

      def excludeN(): Unit = {
        if (depths(n) == fusionDepth & delta > 0) {
          debugln(s"Adding nester $n ${n.op.hiOp}")
        }
        debugln(s"Adding terminator $n ${n.op.hiOp}")
        flatteners += n
        exclude += n
      }


      if (depths(n) == fusionDepth) {
        if (delta > 0) {
          excludeN()
        } else if (n.op.isNestedReduction || n.op.blockArrayFusion) {
          excludeN()
        }

        if (mustBeExcluded(n))
          excludeN()
      } else if (n.inputs.isEmpty) {
        excludeN()
      } else if (depths(n) == fusionDepth - 1 && delta < 0) {
        excludeN()
      } else if (depths(n) == fusionDepth && n.seenBy.isEmpty) {
        excludeN()
      } else if (depths(n) < fusionDepth) {
        excludeN()
      } else if (n.seenBy.isEmpty) {
        debugln(s"Implicit terminator $n ${n.op.hiOp}")
        flatteners += n
      }

      if (n.op.nonFusable) excludeN()
    }

    (flatteners, exclude)
  }

  private lazy val cliques = {
    dag
      .cliques(terminators = flatteners, exclude=exclude)
      .map(c => HiClique(interior = c.interior -- exclude))
      .filter(_.interior.size > 1)
      .filter(_.bottom.nonEmpty)
  }
}
