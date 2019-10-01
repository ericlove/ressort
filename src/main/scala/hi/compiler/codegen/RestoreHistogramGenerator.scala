package ressort.hi.compiler
import ressort.hi
import ressort.lo._
import ressort.hi.compiler._
import ressort.compiler._

case class RestoreHistogramGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "RestoreHistogram"

  def emit(
      inputs: List[ArrayView],
      output: ArrayView,
      op:     hi.RestoreHistogram): LoAst = {
    val rhpi = {
      new RestoreHistogramProblemInstance(
        input     = inputs.tail.head,
        op        = op,
        elaboration = elaboration)
    }
    rhpi.restore
  }
}

class RestoreHistogramProblemInstance(
    val input:      ArrayView,
    val op:         hi.RestoreHistogram,
    val elaboration:  Elaboration)
  extends HistogramOperatorInstance {

  // Parameters to HistogramOperatorInstance
  def slices = {
    throw new Error(
      "Should never use `slices` in `RestoreHistogramProblemInstance`")
  }
  val hist = input
  val output = input
  val msb = None
  val lsb = None
  override def parallel = op.parallel


  def restore: LoAst = {
    val rest = if (parallel) restoreMulti else restoreSingle

    rest +
    printHist("Post-Restore")
  }

  def restoreSingle: LoAst = {
    val i = elaboration.tempIds.newId("i")
    val a = elaboration.tempIds.newId("a")
    val b = elaboration.tempIds.newId("b")

    (a := (Index(), Const(0))) +
    (b := (Index(), Const(0))) +
    ForBlock(i, hist.maxCursor,
        (a := hist.access(i)) +
        (hist.access(i) :=  b) +
        (b := a))
  }
/**
  def restoreSingle: LoAst = {
    hist.globalState +
    hist.resetLocalState +
    RotRight(
      Deref(hist.array.buffer.name),
      Const(1),
      Some(ArrOpRange(hist.offset, hist.offset + hist.maxCursor))) +
    (hist.access(0) := Const(0))
  }
  **/

  def restoreMulti: LoAst = {  
    val i = elaboration.tempIds.newId("i")
    val j = elaboration.tempIds.newId("j")
    val myHist = hist.asInstanceOf[SlicedArray.View]
    val base = myHist.base
    val a = elaboration.tempIds.newId("a")
    val b = elaboration.tempIds.newId("b")

    (a := (Index(), Const(0))) +
    (b := (Index(), Const(0))) +
    ForBlock(i, myHist.maxCursor,
      ForBlock(j, myHist.numArrays,
        (a := base.access((j * myHist.physVecLen) + i)) +
        (base.access((j * myHist.physVecLen) + i) :=  b) +
        (b := a)))
  }
}

