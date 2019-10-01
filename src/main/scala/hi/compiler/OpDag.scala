// See LICENSE.txt
package ressort.hi.compiler
import scala.collection.mutable.{HashSet, HashMap, Queue, LinkedHashSet}
import ressort.hi
import ressort.lo


/** Holds a HiRes or LoRes operator Dag at various stages of elaboration.
  *
  * @tparam A The type of array, or level of data representation, on which
  *           this DAG's operators act.
  *
  * @tparam O The level of operator representation contained within this DAG,
  *           which may be [[ressort.hi.Operator]]s or various lowerings to
  *           [[ressort.lo.LoAst]]s.
  */
trait OpDag[A, O, +D <: OpDag[A, O, D]] { this: D =>
  /** The operator held by this node of the Dag */
  def op: O
  
  /** All inputs feeding into this nodes' operator.
    *
    * Inputs __must__ appear in the order defined by the HiRes operator's syntax;
    * if an operator has the form `Op(a, b, c)`, then the DAG nodes correspdonding
    * `a`, `b`, and `c` must appear in `inputs` in that order.
    */
  def inputs: List[D]
 
  /** The data structure representing the output of this operation */
  def output: A
  
  /** The internal Dag if this is a fused Dag node */
  def internalDag: Option[D]

  /** A unique identifier used to track this node across all phases of transformation */
  var nodeId: Option[Integer]=None

  /** Returns a [[scala.collection.Seq]] of the results of applying function `f` to each
    * node in the Dag as seen in a depth-first, post-order traversal.
    */
  private def depthFirstEither[T](preOrder: Boolean)(f: D => T): Seq[T] = {
    val visited = HashSet[D]()
    var seq = Seq[T]()

    def visit(node: D) {
      if (!visited.contains(node)) {
        visited += node
        if (preOrder) {
          seq = f(node) +: seq
          node.inputs.map(visit)
        } else {
          node.inputs.map(visit)
          seq = f(node) +: seq
        }
      }
    }
    visit(this)

    seq.reverse
  }

  /** Returns a [[scala.collection.Seq]] of the results of applying function `f` to each
    * node in the Dag as seen in a depth-first, post-order traversal that
    * visits each node exactly once.
    */
  def depthFirst[T](f: D => T): Seq[T] = depthFirstEither(preOrder=false)(f)

  /** Returns a [[scala.collection.Seq]] of the results of applying function `f` to each
    * node in the Dag as seen in a depth-first, pre-order traversal that
    * visits each node exactly once.
    */
  def depthFirstPre[T](f: D => T): Seq[T] = depthFirstEither(preOrder=true)(f)

  /** Returns a [[scala.collection.Seq]] of all nodes at the top of the
    * Dag -- that is, nodes without any inputs.
    */
  def top: Seq[D] = {
    var nl = List[D]()
    depthFirst {
      n => if (n.inputs.isEmpty) nl = n :: nl
    }
    nl.reverse.toSeq
  }

  /** Prints out the structure of a Dag for debugging
    *
    * @param indent Number of tabstops to indent the output
    */
  def print(indent: Int = 0): Unit = {
    assert(indent < 10)
    val maxChar = 500
    val maxLine = 2000
    // Note: instead of using default string building, optimize performance by collecting per-node
    // stringifications and then assemble a final buffer to minimize allocations.
    val builder = new StringBuilder()
    val ind = "  "
    def trav(node: D, indent: Int): Unit = {
      node.depthFirst { node =>
        val inline = ind * indent
        val newIndent = "\n" + inline
        val subIndent = newIndent + ind
        val array: Option[MetaArray] = node.output match {
          case ra: MetaArray => Some(ra)
          case _ => None
        }
        val view: Option[ArrayView] = node match {
          case l: LoDag => Some(l.outputView)
          case _ => None
        }
        val op = node.op match {
          case rop: HiArrayOp => rop.hiOp
          case other => other
        }
        val cursors = node match {
          case h: HiDag if h.internalDag.nonEmpty => h.cursors.mkString(", ")
          case _ => ""
        }
        
        val opStr = op.toString
        val dots = if (opStr.length > maxChar) " [...]" else ""
        val nodeStr = node.nodeId.getOrElse(node.toString)
        val outType = node match {
          case d: HiDag => d.op.typed.funcType.to.toString
          case _ => ""
        }
        builder ++= s"$newIndent ($nodeStr) ${opStr.take(maxChar)}$dots\n"
        if (node.isInstanceOf[HiDag]) {
          builder ++= s"$inline\tOutput type: ${outType.take(maxLine)}\n"
          builder ++= s"$inline\tCursors: [$cursors]\n"
        }
        if (view.isEmpty) {
          array.map(a => builder ++= a.mkString(indent+5))
          builder ++= "\n"
        }
        view.map(v => builder ++= s"\n${v.mkString(indent+5)}")
        node.internalDag.map(trav(_, indent+8))
      }
    }
    trav(this, indent+2)
    println(builder.toString)
  }

  def headNode: D = this.inputs.headOption.map(_.headNode).getOrElse(this)
}

object OpDag {
  var debug: Boolean = false
}


/** A mutable [[ressort.compiler.OpDag]] that also tracks reverse edges
  *
  * This is useful for most DAG transformations, as they will require knowledge of
  * which nodes depend on (i.e. are ''seen by'') a given node, and they will also
  * need to make edits to the DAG by inserting or removing nodes.
  */
trait DoublyLinkedDagLike[A, O, D <: DoublyLinkedDagLike[A, O, D]] extends OpDag[A, O, D] { this: D =>
  var op: O
  var inputs: List[D]
  var seenBy: List[D]
  var output: A
  var internalDag: Option[D]

  private def detectCycle(old: Seq[D]): Unit = {
    val visited = HashSet[D]()
    breadthFirstTraverse { node =>
      if (visited.contains(node)) {
        println(s"Added cycle in DAG by setting inputs or outputs of ${this.asInstanceOf[HiDag].op.hiOp}")
        println(s"Node ${node.asInstanceOf[HiDag].op.hiOp} - $node already seen!")
        println(s"Old Values:")
        old.map(_.asInstanceOf[HiDag].op.hiOp.toString).map(println)
        println()
        println(s"New Values:")
        inputs.map(n => n.asInstanceOf[HiDag].op.hiOp.toString + s" - $n").map(println)
        println()
        println("DAG:")
        depthFirstPre { n =>
          println(s"\t${n.asInstanceOf[HiDag].op.hiOp} - $n")
          n.inputs.map { i => println(s"\t\t${i.asInstanceOf[HiDag].op.hiOp} - $i") }
        }
        ???
      }
      println(s"Visiting Node ${node.asInstanceOf[HiDag].op.hiOp} - $node")
      visited += node
    }
    println()
    println()
  }

  /** Sets the `seenBy` list of each node in this DAG based on forward edges. */
  def fillBackwardEdges(): Unit = {
    // First, clear all `seenBy` lists
    depthFirst(_.seenBy = Nil)

    // Then, add each node to its inputs' `seenBy` lists
    depthFirst { n =>
      n.inputs.map(_.seenBy +:= n)
    }

    // Finally, remove duplicates from `seenBy` lists and sort in topological order
    val dagOrder = depthFirstPre(i => i).zipWithIndex.toMap
    depthFirst { n =>
      n.seenBy = n.seenBy.distinct.sortBy(dagOrder)
      n.internalDag.map(_.fillBackwardEdges)
    }
  }

  def breadthFirstTraverse[T](f: D => T): Seq[T] = {
    DoublyLinkedDagLike.breadthFirstTraverse[A, O, D, T](this :: Nil)(f)
  }

  def breadthFirstReverse[T](f: D => T): Seq[T] = {
    DoublyLinkedDagLike.breadthFirstTraverse[A, O, D, T](top, reverse=true)(f)
  }

  /** Returns a map from each node to the set of nodes it dominates,
    * or, if `reverse` is set, to the set of nodes dominating it
    */
  def dominatorSets(reverse: Boolean=false): Map[D, Set[D]] = {
    val dmap = HashMap[D, Set[D]]()
    breadthFirstReverse(dmap(_) = Set[D]())

    if (reverse) {
      breadthFirstReverse { n =>
        n.seenBy.map(
          i => {
            assert(
              dmap.contains(i),
              s"$i ${i.asInstanceOf[HiDag].op.hiOp} missing for node $n ${n.asInstanceOf[HiDag].op.hiOp}")
            dmap(i) ++= dmap(n) + n
          })
      }
    } else {
      breadthFirstTraverse { n =>
        n.inputs.map(i => dmap(i) ++= dmap(n) + n)
      }
    }

    dmap.toMap
  }

  /** A segment of this DAG represented as a triple of node types.
    *
    * These classifications are particular to a given fusion algorithm,
    * which must define them as arguments to [[cliques]].
    * The nodes of `interior` are those that do not appear in either other set.
    */
  case class Clique(starters: Set[D], terminators: Set[D], interior: Set[D]) {
    override def toString: String = {
      var s = "Clique(\n"
      s += "Starters:\n"
      starters.map(n => s += s"\t${n.asInstanceOf[HiDag].op.hiOp}\n")
      s += "Interior:\n"
      interior.map(n => s += s"\t${n.asInstanceOf[HiDag].op.hiOp}\n")
      s += "Terminators:\n"
      terminators.map(n => s += s"\t${n.asInstanceOf[HiDag].op.hiOp}\n")
      s += ")"
      s
    }
  }

  /** Returns a sequence of [[Clique]]s as defined by the standard algorithm
    *
    * The `terminators` and `exclude` parameters indicate which nodes could
    * end a fused node.  Their definition will vary
    * for different kinds of fusion (e.g. vector vs. array), and different
    * fusion cases will differ in terms of whether or not terminators
    * (or other nodes) are allowed _within_ the clique.  The `exclude` set keeps such
    * nodes out of the interior, while allowing all others, including 
    * terminators if not marked.
    *
    * @param terminators Nodes that must break a clique, forming a boundary
    * @param exclude These nodes must never be included inside a clique's interior
    */
  def cliques(terminators: Set[D], exclude: Set[D]=Set()): Seq[Clique] = {
    val dominates = dominatorSets()
    val dominators = dominatorSets(reverse=true)
    implicit object DagOrdering extends Ordering[D] {
      val dagOrder = depthFirstPre(n=>n).zipWithIndex.toMap

      def compare(a: D, b: D) = dagOrder(a) compare dagOrder(b)
    }
    val marked = HashSet[D]()
    val dagOrder = depthFirstPre(n=>n).zipWithIndex.toMap
    val t = LinkedHashSet[D]()
    t ++= terminators.toSeq.sortBy(dagOrder)
    val allStartTerm = terminators

    var cliques = Seq[Clique]()

    def debugln(s: String="") { if (OpDag.debug) println(s) }
    while (t.nonEmpty) {
      val tdoms = {
        var set = Set[D]()
        t.map(n => set ++= dominates(n))
        set
      }
      val term = t.filter(!tdoms.contains(_)).head
      var tnext = Set[D](term)
      var tcliq = Set[D](term)
      var snext = Set[D]()
      var scliq = Set[D]()
      debugln(s"CLIQUE FOR TERMINATOR: ${term} : ${term.asInstanceOf[HiDag].op.hiOp}")
      debugln(s"Inputs:")
      term.inputs.map(n => debugln(s"\t$n : ${n.asInstanceOf[HiDag].op.hiOp} marked? ${marked.contains(n)}"))
      debugln("-")

      while (tnext.nonEmpty || snext.nonEmpty) {
        // Compute next set of starters to (possibly) add to clique:
        //  = all terminators that dominate a terminator currently in the clique
        snext = ((tcliq).map(dominators).foldLeft(Set[D]())(_ ++ _)) -- scliq
        snext = snext.filter(n => !t.exists(dominators(n).contains(_)))
        scliq ++= snext

        // Compute next set of terminators to (possibly) add to clique:
        //  = all terminators dominated by a term currently in the clique
        tnext = (scliq.map(dominates).foldLeft(Set[D]())(_ ++ _) & t) -- tcliq
        tnext = tnext.filter(n => !tcliq.exists(dominators(n).contains(_)))
        tnext = tnext.filter(n => !tnext.exists(dominators(n).contains(_)))
        debugln(s"Next terminators:")
        tnext.map(_.asInstanceOf[HiDag]).map(n => debugln(s"$n : ${n.op.hiOp}"))
        tcliq ++= tnext
      }
      val interior = {
        val sdom = scliq.map(dominates(_)).foldLeft(Set[D]())(_ ++ _)
        val tdom = tcliq.map(dominates(_)).foldLeft(Set[D]())(_ ++ _)

        // All unmarked nodes that (1.) are dominated by at least one term
        // and (2.) are not dominated by any terminator
        val init = (sdom -- tdom) -- marked -- t
        init ++ tcliq -- marked
      }
      marked ++= interior
      marked += term
      val clique = Clique(starters = scliq, terminators = tcliq, interior = interior)
      debugln(s"Made Clique:")
      clique.interior.map(n => debugln(s"$n : ${n.asInstanceOf[HiDag].op.hiOp}"))
      cliques +:= clique

      // `isEmpty` test needed to exclude virtual inputs that won't have been marked in
      // `exclude` because they were added after the original analysis
      val trem = t.filter(_.inputs.forall(n => marked.contains(n) || exclude.contains(n) || n.inputs.isEmpty))
      marked ++= trem

      t --= trem
    }

    cliques
  }
}


object DoublyLinkedDagLike {
  def apply[A, O, D <: DoublyLinkedDagLike[A, O, D], D1 <: OpDag[A, O, D1]](
      single: OpDag[A, O, D1])
      (constructor: (O, A) => D): D = {

    // First, create a new node for each original in `single`, and save
    // the old-to-new mapping.
    val newNodeFor = HashMap[OpDag[A, O, D1], D]()
    single.depthFirst { n =>
      val d = constructor(n.op, n.output)
      d.inputs      = Nil
      d.seenBy      = Nil
      d.internalDag = n.internalDag.map(DoublyLinkedDagLike(_)(constructor))
      newNodeFor(n) = d
    }
    Map() ++ newNodeFor

    // Then, fill in forwards edges in the new DAG
    single.depthFirst { n =>
      val dldNode = newNodeFor(n)
      val dldInputs = n.inputs.map(newNodeFor)
      dldNode.inputs = dldInputs
    }

    val double = newNodeFor(single)
    double.fillBackwardEdges()
    double
  }

  def breadthFirstTraverse[A, O, D <: DoublyLinkedDagLike[A, O, D], T](
      frontier: Traversable[D],
      reverse: Boolean=false)
      (f: D => T): Seq[T] = {
    var curFront = frontier.toSeq
    var res = Seq[T]()
    val marked = HashSet[D]()
    while (curFront.nonEmpty) {
      var nextFront = Seq[D]()
      marked ++= curFront
      for (n <- curFront) {
        res +:= f(n)
        val next = if (reverse) n.seenBy else n.inputs
        for (m <- next) {
          val edges = if (reverse) m.inputs else m.seenBy
          if (edges.forall(marked.contains(_)) && !nextFront.contains(m))
            nextFront +:= m
        }
      }
      curFront = nextFront
    }
    res
  }
}
