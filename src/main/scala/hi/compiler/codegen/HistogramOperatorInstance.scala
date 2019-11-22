// See LICENSE.txt
package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._;
import ressort.hi

/** Provides functionality useful to all code generators that deal
  * with histogram-based partitioning.
  */
trait HistogramOperatorInstance {
  /** Histogram this operator creates, updates, or uses */
  def hist: ArrayView

  def elaboration: Elaboration
  
  /** Indicates that this operator uses a multi-threaded histogram */
  def parallel: Boolean = false

  private lazy val tempIds = elaboration.tempIds
  private lazy val config = elaboration.config.rpart

  private lazy val i     = tempIds.newId("i")
  private lazy val j     = tempIds.newId("j")
  private lazy val tmp   = tempIds.newId("tmp")
  private lazy val acc   = tempIds.newId("acc")


  /** Returns code to print a histogram for debugging purposes */
  def printHist(location: String=""): LoAst = {
    if(config.debug) {
      Printf("-----------------") +
      Printf(location) +
      Printf("Histogram contents:") +
      ForBlock(i, hist.maxCursor,
        Printf("\t-> %d", hist.access(i))) +
      Printf("-----------------")
    } else {
      Nop
    }
  }

  /** Returns code to print the records in a histogram-partitioned structure */
  def printRecs(slices: ArrayView, location: String=""): LoAst = {
    if(config.debug) {
      Printf("-"*20) +
      Printf(location) +
      Printf("Partitioned Relation:") +
      (acc := (Index(), -1)) +
      ForBlock(i, hist.maxCursor-1,
        Printf("\n\t Partition %d:", i) +
        Printf("\t" + ("-"*10)) +
        ForBlock(j, hist.access(i+1) - hist.access(i) ,
          (acc := acc + 1) +
          Printf("\t\t%d (%d):\t%x", j, acc,
            LowerWord(slices.access(hist.access(i)+j)))))
    } else {
      Nop
    }
  }

  import HistogramOperatorInstance.HistStreamRecord

  /** Processes all the records in the input window, and calculates their
    * respective partitions.  Also applies input function to process each 
    * record.
    *
    * @param keys     Key values that determine which partition in which to place a record
    *
    * @param values   The actual records to be stored in partitions
    *
    * @param process  Function to apply to each record and its partition
    *                 number to generate an [[LoAst]] that processes them.
    */
  def streamRelSerial(keys: ArrayView, values: ArrayView, cursor: Expr)
      (process: HistStreamRecord => LoAst): LoAst = {
    val key = keys.access(cursor)
    val value = values.access(cursor)
    val part  = tempIds.newId("part")
    val pexpr = keys.access(cursor)
    val hsr = HistStreamRecord(part, cursor, value)
    val update = DecAssign(part, Index(const=true), pexpr) + process(hsr)
    keys.readMask(hsr.index) match {
      case Some(m) => If(m, update)
      case None => update
    }
  }
}

object HistogramOperatorInstance {
  case class HistStreamRecord(part: Expr, index: Expr, rec: Expr)
}
