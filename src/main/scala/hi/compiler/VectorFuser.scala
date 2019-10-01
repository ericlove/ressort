// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi
import scala.collection.mutable.{HashMap, LinkedHashSet, SortedSet}
import scala.collection.mutable


class VectorFuser(arrayGen: OutputArrayGenerator) extends HiDagTransform[HiDag] {
  def updateDag(dag: HiDag): HiDag = {
    debugln(s"------ BEGIN VECTOR FUSE -----")
    updateDagHelper(dag)
    debugln(s"BEGIN OUTPUT REGEN ----")

    dag.depthFirst { n => n.regenerateFromInputs(arrayGen) }
    debugln(s"------ END VECTOR FUSE -----")

    dag
  }

  private def debugln(s: String="") {
    if (OpDag.debug)
      println(s)
  }

  private def updateDagHelper(dag: HiDag, doInternal: Boolean=true): Unit =  {
    def getInternal(d: HiDag): Set[HiDag] = {
      val internal = d.depthFirst(_.internalDag).flatten
      val next = for (i <- internal) yield {
        val ii = getInternal(i)
        if (ii.isEmpty) {
          Set(i)
        } else {
          ii
        }
      }
      next.flatten.toSet ++ internal
    }

    if (doInternal)
      getInternal(dag).map(updateDagHelper(_, false))

    val segmenter = new VectorSegmenter(dag)
    val cliques = segmenter.doSegmentation()
    if (!cliques.isEmpty) {
      // Fusion Depth is always zero for vector fusion, by definition
      val fuser = new HiDagFuser(cliques, 0, true, arrayGen)
      val fused = fuser.updateDag(dag)
      fused.map(disableLastLoops)
    }
  }

  private def disableLastLoops(node: FusedNode) {
    node.clique.bottom.head.depthFirst { n =>
      n.op = n.op.copy(lastLevelLoop = false)
    }
  }
}

class VectorSegmenter(dag: HiDag) {
  import HiDagTransform._
  def doSegmentation(): Seq[HiClique] = {
    val clist = cliques
    debugln("VECTOR FUSION CLIQUE LIST:")
    for (s <- clist) {
      debugln(s"\t-- ${s.bottom.head.op.hiOp}")
    }
    debugln("-"*90)
    debugln()
    cliques
  }

  private def debugln(s: String="") {
    if (OpDag.debug)
      println(s)
  }


  private def materialOutput(d: HiDag): Boolean = {
      d.op.blockingOutput//     ||
      //d.op.controlsOutputCursor
  }

  private def mustBeExcluded(d: HiDag): Boolean = {
    val res = 
      d.inputs.isEmpty ||
      d.seenBy.isEmpty ||
      d.internalDag.nonEmpty  ||
      d.op.hiOp.isInstanceOf[hi.Uncat] ||
      d.op.hiOp.isInstanceOf[hi.Cat] ||
      d.op.hiOp.isInstanceOf[hi.Flatten] ||
      d.op.hiOp.isInstanceOf[hi.Split] ||
      d.op.hiOp.isInstanceOf[hi.Block] ||
      d.op.hiOp.isInstanceOf[hi.DagOp] ||
      !allLevelsLinked(d)
    res
  }

  /** Returns true iff all but the depth-zero level of `node` is linked
    *
    * This is a necessary constraint on flat-array fusion because failure to
    * sub-array fuse any level of a node in `seg` necessarily precludes flat-
    * array fusion: otherwise, extra loops would be emitted.
    */
  private def allLevelsLinked(node: HiDag): Boolean = {
    val op = node.op.hiOp
    val nodeDepth = node.output.depth
    for (i <- 1 to nodeDepth) {
      if (!node.cursors.contains(i) && 
         !(i == nodeDepth &&
            node.op.raisesNestingLevel &&
            !node.op.lowersNestingLevel)) {
        return false
      }
    }
    true
  }

  private lazy val (terminators, excluded) = {
    val terminators = LinkedHashSet[HiDag]()
    val excluded = LinkedHashSet[HiDag]()
    terminators += dag
    this.dag.depthFirst { n =>
      if (materialOutput(n) && (allLevelsLinked(n))) {
        terminators += n
      }

      if (mustBeExcluded(n) && allLevelsLinked(n)) {
        excluded += n
        terminators += n
      } else if (mustBeExcluded(n)) {
        excluded += n
        terminators += n
      }

      if (n.seenBy.isEmpty && allLevelsLinked(n)) {
        terminators += n
      }
    }
    (terminators.toSet, excluded.toSet)
  }

  private lazy val cliques = {
    dag
      .cliques(terminators = terminators, exclude = excluded)
      .map(c => HiClique(interior = c.interior -- excluded))
      .filter(_.interior.size > 1)
      .filter(_.bottom.nonEmpty)
      .filter(_.top.nonEmpty)
  }

}
