// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi
import ressort.lo._
import ressort.hi.compiler._
import ressort.compiler._

/** Generates LoRes code for the [[hi.Offsets]] operator */
case class ReduceGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "Reduce"

  def emit(
      input: RecParallelIO,
      output: RecParallelIO,
      nested: Boolean,
      op: hi.Reduce): LoopLevel = {
    // NOTE: CodeGeneratorFacade initializes accumulator
    val accVar = elaboration.tempIds.newId("acc")
    val acc = if (nested) output.currentRec else accVar
    val next = input.currentRec
    val initVar = elaboration.tempIds.newId("init")
    val expr = op.op match {
      case hi.PlusOp => acc + next
      case hi.MulOp => acc * next
      case hi.MinOp => Mux(acc < next, acc, next)
      case hi.MaxOp => Mux(acc > next, acc, next)
      case hi.AndOp => acc && next
      case hi.OrOp => acc || next
    }
    val setMask = output.setMask(True)
    val initMask = output.setMask(False)
    val finalizer = if (nested) Nop else (output.currentRec := accVar)
    op.init match {
      case Some(i) => {
        LoopLevel(
          body = (acc := expr) + setMask,
          initializer = (if (nested) Nop else (accVar := (output.recType, Expr(i)))) + initMask,
          finalizer = finalizer)
      }
      case None => {
        LoopLevel(
          body =
            IfElse(
              initVar,
              (acc := expr) + setMask,
              (initVar := True) + (acc := next)),
          initializer = (initVar := (Bool(), False)) + initMask + Dec(accVar, output.recType),
          finalizer = finalizer)
      }
    }
  }
}

