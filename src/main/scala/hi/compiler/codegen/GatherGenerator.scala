// See LICENSE.txt
package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._
import ressort.hi

case class GatherGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "gath"


  def emit(
      indices: RecParallelIO,
      target: ArrayView,
      output: RecParallelIO,
      op: hi.Gather): LoAst = {
    if (op.absolute)
      (output.currentRec := target.absolute(indices.currentRec))
    else
      (output.currentRec := target.access(indices.currentRec))
  }
}
