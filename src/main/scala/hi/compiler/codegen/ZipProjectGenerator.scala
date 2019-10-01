// See LICENSE.txt
package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._
import ressort.hi

case class ZipProjectGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {

  val generatorName = "zipproj"


  def emit(
      inputs: List[RecParallelIO],
      output: RecParallelIO,
      op: hi.Operator): LoAst = {
    var curGroup = 0
    var curOutField = 0
    val assignBlocks: Seq[Seq[LoAst]] = for (accessor <- inputs) yield {
      val inRec = accessor.currentRec
      val outRec = output.currentRec
      def assignFields(inFieldTypes: Seq[Record.Field], rec: Boolean): Seq[LoAst] = {
        val assigns = for ((f, n) <- inFieldTypes.zipWithIndex) yield {
          val (inField, outField) = f.name match {
            case _ if rec => (UField(inRec, n), UField(outRec, curOutField))
            case _ => (inRec, UField(outRec, curOutField))
          }
          curOutField += 1
          (outField := inField)
        }
        assigns
      }
      accessor.recType match {
        case r: Record => (assignFields(r.fields, true))
        case f: Record.Field => (assignFields(Seq(f), false))
        case n: NonRec => (assignFields(Seq(Record.Field(n)), false))
        case _ => throw new AssertionError(s"shouldn't have type ${accessor.recType}")
      }
    }
    Block(assignBlocks.toList.flatten)
  }
}
      

