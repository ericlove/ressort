// See LICENSE.txt
package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._
import ressort.hi

case class MaskGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "sel"

  def emit(
      values: RecParallelIO,
      cond: RecParallelIO,
      output: RecParallelIO,
      op: hi.Mask): LoAst = {
    val outExpr = values.currentMask match {
      case Some(m) => m && cond.currentRec
      case None => cond.currentRec
    }
    output.setMask(outExpr)

  }
}
