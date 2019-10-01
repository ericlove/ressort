package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._
import ressort.hi

case class CollectGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "sel"

  def emit(
      input: RecParallelIO,
      output: StreamingIO,
      op: hi.Collect): LoAst = {

    IfElse(
      input.currentMask.get,
      ifBody = 
        (output.currentRec := input.currentRec) + (output.advanceRec),
      elseBody =
        Nop)

  }
}
