// See LICENSE.txt
package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._;
import ressort.hi
import scala.collection.mutable.HashMap

case class CompactGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "compact"

  def emit(
      input: RecParallelIO,
      output: ArrayView,
      outCursor: SymLike,
      op:     hi.Compact): LoAst = {
    (output.access(outCursor) := input.currentRec) + (outCursor := outCursor + 1)
  }
}
