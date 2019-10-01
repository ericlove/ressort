// See LICENSE.txt
package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._
import ressort.hi

case class GatherGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "sel"


  def emit(
      indices: RecParallelIO,
      target: IndexableIO,
      output: RecParallelIO,
      op: hi.Gather): LoAst = {
    (output.currentRec := target.index(indices.currentRec))
  }
}
