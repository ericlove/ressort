// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi
import ressort.lo._
import ressort.compiler._

/** Holds one input our output to a generator instance */
sealed abstract class GeneratorIO(private val view: ArrayView) {
  def recType: Primitive = view.array.recType
}

/** Allows access to arbitrary indices in the current vector */
class IndexableIO(view: ArrayView) extends GeneratorIO(view) {
  def index(i: Expr): LValue = view.access(i)

  def indexMask(i: Expr): Option[Expr] = view.readMask(i)
}

/** This represents a strictly one-to-one relationship between the operator's
  * controlling cursor and indices into this array.
  */
class RecParallelIO(view: ArrayView, index: Expr) extends GeneratorIO(view) {
  def currentRec: LValue = view.access(index)

  def currentMask: Option[Expr] = view.readMask(index)

  def setMask(value: Expr): LoAst = view.setMask(index, value)

  def firstRec: LValue = view.access(Const(0))

  def zeroMask: Option[Expr] = view.readMask(Const(0))
}

/** A accessor whose cursor is advanced by the operator */
class StreamingIO(view: ArrayView, index: LValue) extends GeneratorIO(view) {
  def currentRec: LValue = view.access(index)

  def currentMask: Option[Expr] = view.readMask(index)

  def advanceRec: LoAst = (index := index + Const(1))
}

/** Generates code that processes LoRes arrays via a accessor interface.
  *
  * Each HiRes primitive operator has a corresponding code generator that
  */
trait CodeGenerator {
  /** String that identifies this generator and the algorithm it encodes */
  def generatorName: String
 
  /** Elaboration context for this generator */
  def elaboration: Elaboration
  
  /** LoRes symbol allocator that all code generation logic should use */
  lazy val tempIds = {
    class ExtendedTempIds(prefix: String) extends TempIds {
      override def newId(name: String): SymLike = {
        elaboration.tempIds.newId(prefix+"_"+name)
      }
    }
    new ExtendedTempIds(generatorName)
  }
  
}
