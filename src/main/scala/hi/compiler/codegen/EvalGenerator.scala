package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._
import ressort.hi

case class EvalGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "eval"


  def emit(
      input: RecParallelIO,
      output: RecParallelIO,
      op: hi.Eval): LoAst = {
    val id = elaboration.tempIds.newId("rec")
    implicit val implicitRec: Option[(SymLike, Primitive)] = Some(id, input.recType)
    val expr = Expr(op.func)(implicitRec)
    If(
      True,
      Block(List(
        (id := (input.recType, input.currentRec)),
        (output.currentRec := expr))))
  }
}
      

