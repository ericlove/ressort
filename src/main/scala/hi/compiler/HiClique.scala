// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi
import scala.collection.mutable.{HashMap, LinkedHashSet}
import scala.collection.mutable


/** Represents a clique of nodes in a [[HiDag]] to be fused
  *
  * @param interior  All the nodes contained within the operator to be fused
  *
  * @param bottom All internal nodes with at least one externally-visible output
  *
  * @param top All internal nodes with at least one exterior input
  *
  */
case class HiClique(interior: Set[HiDag]) {
  import HiClique._

  def top: Set[HiDag] = interior.filter(n => n.inputs.exists(!interior.contains(_)) || n.inputs.isEmpty)
  def bottom: Set[HiDag] = interior.filter(n => n.seenBy.exists(!interior.contains(_)) || n.seenBy.isEmpty)

  def above: Set[HiDag] = top.map(_.inputs).flatMap(_.filter(!interior.contains(_)))
  def below: Set[HiDag] = bottom.map(_.seenBy).flatMap(_.filter(!interior.contains(_)))

  /** Returns a set of internal nodes seen by nodes outside of the segment. */
  lazy val externallyVisible: Set[HiDag] =
    interior.filter(n => n.seenBy.exists(!interior.contains(_)) || n.seenBy.isEmpty)

  /** Returns the net change in nesting of this segment,
    * positve if it increases, negative if it decreases.
    */
  def nestingLevelChange: Int = {
    def walk(d: HiDag, n: Int): Int = if (!d.inputs.isEmpty && interior.contains(d.inputs.head)) {
      val input = d.inputs.head
      if (d.op.raisesNestingLevel && !d.op.lowersNestingLevel)
        walk(input, n+1)
      else if (d.op.lowersNestingLevel && !d.op.raisesNestingLevel)
        walk(input, n-1)
      else
        walk(input, n)
    } else {
      n
    }
    val res = bottom.map(walk(_, 0)).max
    res
  }

  def print(): Unit = {
    println(s"ABOVE:")
    above map { n => println(s"\t$n ${n.op.typed.o}") }
    println(s"TOP:")
    top map { n => println(s"\t$n ${n.op.typed.o}") }
    println("INTERIOR:")
    interior map { n => println(s"\t$n ${n.op.typed.o}") }
    if (bottom.nonEmpty) {
      println(s"BOTTOM:\n(ext-vis) [${bottom.head.op.typed.o}]")
      for (o <- Set(bottom.head) ++ bottom.tail) {
        println(s"\t$o ${o.op.typed.o}")
        for (s <- o.seenBy) {
          val str = if (interior.contains(s)) "" else "-X-"
          println(s"\t\t$s ${s.op.typed.o} $str")
        }
      }
    }
    println("BELOW:")
    below map { n => println(s"\t$n ${n.op.typed.o}") }
    println()
    println()
  }
}

