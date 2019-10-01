// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi
import scala.collection.mutable.HashMap

/** Balances the nesting depth of inputs to multi-input nodes
  *
  * Wherever a node accepts two or more inputs with different degrees of nesting,
  * `InsertShellNodes` inserts an empty node with an `EmptyShellArray` as its output
  * `HiArray` to balance the nodes' nesting depths, or multiple such nodes if
  * the difference in degree of nesting is greater than one.
  */
class InsertShellNodes extends HiDagTransform[HiDag] {
  import HiDagTransform._

  def updateDag(dag: HiDag): HiDag = {
    new Insertion(dag).update()
    dag
  }

  private class Insertion(dag: HiDag) {


    def update() {
      dag.depthFirstPre { node =>
        if (node.inputs.length > 1) {
          // Figure out how deep each input is supposed to be based on `arrayInputs`: 
          // By subtracting 1 from the real depth of each array-input, we enforce that
          // another layer will be added if it is not aligned correctly with other inputs
          val pseudoDepths = for ((i, a) <- node.inputs.zip(node.op.arrayInputs)) yield {
            if (a) depths(i) - 1 else depths(i)
          }
          val nodeDepth = pseudoDepths.max
          val newInputs = for ((i, d) <- node.inputs.zip(pseudoDepths)) yield {
            if (d < nodeDepth) {
              var next = i
              for (j <- d to nodeDepth-1) {
                next = insertShellNode(next, node)
              }
              next
            } else {
              i
            }
          }
          node.inputs = newInputs
        }
      }
    }


    /** Degree of nesting of each node's output */
    private lazy val depths = {
      val depths = HashMap[HiDag, Int]()
      dag.depthFirstPre { n =>
        if (!depths.contains(n)) {
          depths(n) = n.output.depth
        }
      }
      depths
    }


    private def insertShellNode(exterior: HiDag, interior: HiDag): HiDag = {
      val name = hi.Id(s"shell_${exterior.output.buffer.name.name}")
      val newHiResOp = hi.DagOp(Some(-3))
      val newArrayOp =
        HiArrayOp(
            typed               = exterior.op.typed.copy(o = newHiResOp),
            raisesNestingLevel  = true,
            materialInputs = List(false),
            arrayInputs = List(false),
            dataParallelOutput = true,
            streamingOutput = true,
            lastLevelLoop = false,
            skipElaboration = true)
      val outputArray = EmptyShellArray(exterior.output)
      val newNode = new HiDag(
        op          = newArrayOp,
        inputs      = List(exterior),
        output      = outputArray,
        allocations = Nil,
        seenBy      = List(interior),
        internalDag = None) {
        
        override def regenerateFromInputs(arrayGenerator: OutputArrayGenerator): Unit = {
          val arrayInputs = inputs.map(_.output)
          val (o, a) = arrayGenerator.apply(op.typed, arrayInputs, nodeId)
          this.output = EmptyShellArray(o)
          this.allocations = a
        }
      }

      depths(newNode) = depths(exterior) + 1
      exterior.seenBy = exterior.seenBy map {
        case x if (x == interior) => newNode
        case other => other
      }
      newNode
    }
  }

}
