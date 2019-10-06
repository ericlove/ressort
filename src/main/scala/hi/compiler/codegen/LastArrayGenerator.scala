// See LICENSE.txt
package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._;
import ressort.hi

case class LastArrayGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "Mrg"

  def emit(
      inputs: List[ArrayView],
      output: ArrayView,
      op:     hi.LastArray): LoAst = {
    val input = inputs.head match {
      case m: MultiArray.View => m.head
      case o => o
    }
    val fhpi = {
      new LastArrayProblemInstance(
        input     = input.asInstanceOf[NestedView with ParallelView],
        output    = output,
        op        = op,
        generator = this)
    }

    fhpi.lastArray
  }
}

class LastArrayProblemInstance(
    val input:      NestedView with ParallelView,
    val output:     ArrayView,
    val op:         hi.LastArray,
    val generator:  LastArrayGenerator) {

  def lastArray: LoAst = {
    val i = generator.elaboration.tempIds.newId("i")
    val j = generator.elaboration.tempIds.newId("j")

    input.globalState +
    output.resetLocalState +
    ForSeq(
        j,
        min = input.numArrays-1,
        max = input.numArrays,
        stride = Const(1),
        body = {
          input.localState(j) +
          ForBlock(i, output.maxCursor,
            output.access(i) := input.access(i))
      })
  }
}
