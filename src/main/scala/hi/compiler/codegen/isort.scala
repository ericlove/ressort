/** Code generator for insertion sort.  
  */
package ressort.hi.compiler
import ressort.compiler._
import ressort.lo._;
import ressort.hi


case class InsertionSortGenerator(
    elaboration: Elaboration)
  extends CodeGenerator {
    
  val generatorName = "isort"
  
  def emit(
      inputs: List[ArrayView],
      output: ArrayView,
      op: hi.InsertionSort): LoAst =  {
    val isgen = {
      new InsertionSortProblemInstance(
        inputs.head,
        output,
        elaboration.tempIds,
        op.keys,
        elaboration.config.isort)
    }
    isgen.genFullSort
  }
}


/** Generates LoRes code for a specific insertion sort problem as specified
  * by the input and output accessors.
  */
class InsertionSortProblemInstance(
    input:    ArrayView,
    output:   ArrayView,
    tempIds:  TempIds,
    keys:     List[hi.FieldName],
    config:   InsertionSortConfig) {
  val recType = input.array.recType

  val i     = tempIds.newId("i")
  val j     = tempIds.newId("j")
  val k     = tempIds.newId("k")
  val idx   = tempIds.newId("idx")
  val tmp   = tempIds.newId("tmp")
  val buf   = tempIds.newId("buf")
  val cond  = tempIds.newId("cond")

  def compareFields(inRec: LValue, outRec: LValue): Expr = {
    def cond(fields: List[hi.FieldName]): Expr = {
      fields match {
        case Nil => False
        case h::t => {
          val (inField, outField) = h match {
            case hi.UFieldName(i) => (UField(inRec, i), UField(outRec, i))
            case hi.NFieldName(i) => (Field(inRec, Id(i.name)), Field(outRec, Id(i.name)))
          }
          (inField < outField) || (Equal(inField, outField) && cond(t))
        }
      }
    }
    cond(keys)
  }

  def genFullSort: LoAst = {
    val comp = compareFields(tmp, output.access(j-1))
    ForBlock(i, input.maxCursor, {
        DecAssign(tmp, recType, input.access(i)) +
        DecAssign(j, Index(), i) +
        ForBlock(k, i,
          If(comp,
            Assign(output.access(j), output.access(j-1)) +
                Assign(j, j-1)
          )
        ) +
        Assign(output.access(j), tmp)
      })
  }
}
