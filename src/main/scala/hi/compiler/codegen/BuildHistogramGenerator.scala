package ressort.hi.compiler
import ressort.hi
import ressort.lo._
import ressort.hi.compiler._
import ressort.compiler._

/** Generates LoRes code for the [[hi.Histogram]] operator.
  *
  */
case class BuildHistogramGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "BuildHistogram"
  
  def emit(
      input: ArrayView,
      output: ArrayView ,
      cursor: Expr,
      op: hi.Histogram): LoAst = {
    val bhpi = {
      new BuildHistogramProblemInstance(
        input,
        output,
        op,
        elaboration)
    }
    bhpi.buildHistSerial(cursor)
  }
}

class BuildHistogramProblemInstance(
    val input: ArrayView,
    val hist: ArrayView,
    val op: hi.Histogram,
    val elaboration: Elaboration)
  extends HistogramOperatorInstance {
  // Parameters to HistogramOperatorInstance
  val slices = input

  /** Generates an LoRes [[LoAst]] to build the histogram. */
  def buildHistSerial(cursor: Expr): LoAst = {
    import HistogramOperatorInstance.HistStreamRecord 
    val countRecs = {
      streamRelSerial(input, input, cursor) { hsr: HistStreamRecord =>
        Increment(hist.access(hsr.part))
      } 
    }
    countRecs + printHist("Post build")
  }

}
