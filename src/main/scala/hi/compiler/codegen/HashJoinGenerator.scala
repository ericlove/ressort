package ressort.hi.compiler

import ressort.hi
import ressort.lo._

case class HashJoinGenerator(elaboration: Elaboration) extends CodeGenerator {

  val generatorName = "hjoin"

  /** Returns a function to insert a [[LoAst]] into the body of the join probe loop */
  def emit(
      left: RecParallelIO,
      right: NestedView with ParallelMacroView,
      hash: RecParallelIO,
      output: ChunkArray.ChunkView,
      op: hi.HashJoin): (LoAst => LoAst) = {
    
    val bucket = elaboration.tempIds.newId("bkt")

    val i = elaboration.tempIds.newId("i")
    val j = elaboration.tempIds.newId("j")
    val leftRec = elaboration.tempIds.newId("lrec")
    val rightRec = elaboration.tempIds.newId("rrec")
    val matchRec = elaboration.tempIds.newId("match")
    val testRec = elaboration.tempIds.newId("test")
    val leftType = left.recType
    val rightType = right.array.recType
    val outType = output.array.recType

    implicit val implicitRec: Option[(SymLike, Primitive)] = Some((testRec, outType))

    def assignFields(dest: LValue, src: LValue, recType: Primitive, right: Boolean=false): LoAst = {
      recType match {
        case rec: Record => {
          var ast: LoAst = Nop
          for ((f, i) <- rec.fields.zipWithIndex) {
            if (op.test.nonEmpty || i != 0) {
              val upd = f.name match {
                case Some(id) => (Field(dest, id) := Field(src, id))
                case None => (UField(dest, i) := UField(src, i))
              }
              ast += upd
            } else if (op.test.isEmpty && i == 0) {
              ast += (UField(dest, 0) := UField(src, 0))
            }
          }
          ast
        }
        case _ if right => {
          // If there is no explicit test, we elide the right key, since this is
          // an equijoin and it will by definition be equal to the left key.
          val skipRightKey = op.test.isEmpty
          val numLeftFields = leftType match {
            case r: Record if skipRightKey => r.fields.length - 1
            case r: Record => r.fields.length
            case _ => 1
          }
          UField(dest, numLeftFields) := src
        }
        case _ => (UField(dest, 0) := src)
      }
    }

    val testMatch = (op.test, rightType) match {
      case (Some(test), _) => Expr(test)(implicitRec)
      case (None, r: Record) => Equal(UField(leftRec, 0), UField(rightRec, 0))
      case (None, _) => Equal(UField(leftRec, 0), rightRec)
    }

    // Function to be returned as output of `emit`
    def builder(ast: LoAst): LoAst = {
      val outputMatch = {
        // Use a different Id from `testRec` so that any fields not used in the
        // test expression will only be loaded from memory if the test succeeds
        Dec(matchRec, outType) +
        assignFields(matchRec, leftRec, leftType) +
        assignFields(matchRec, rightRec, rightType, true) +
        elaboration.states.append(output.cursor.get) +
        (output.access(output.maxCursor-1) := matchRec) +
        ast +
        (output.vectorCursor.get := output.vectorCursor.get + 1)
      }


      val probeLoop = {
        DecAssign(rightRec, rightType, right.access(i)) +
        Dec(testRec, outType) +
        assignFields(testRec, leftRec, leftType) +
        assignFields(testRec, rightRec, rightType) +
        If(testMatch, outputMatch)
      }

      DecAssign(leftRec, leftType, left.currentRec) +
      DecAssign(bucket, Index(), hash.currentRec) +
      right.macroState(bucket) +
      right.windowLoop(probeLoop, Some(i))
    }

    builder(_)
  }
}
