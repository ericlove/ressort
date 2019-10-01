// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi
import ressort.lo._
import ressort.lo.interp.EInt

case class Hash64Generator(elaboration: Elaboration) extends CodeGenerator {

  val generatorName = "hash64"
  private val z = Hash64Generator.z

  def emit(input: RecParallelIO, output: RecParallelIO, op: hi.Hash64): LoAst = {
    val hash = elaboration.tempIds.newId("hash")
    val fields = input.recType match {
      case r: Record => r.fields
      case _ => Seq[Record.Field]()
    }
    multHash(input.currentRec, fields, Const(op.bits.toLong), hash) +
        (output.currentRec := Cast(hash, output.recType))
  }

  def multHash(rec: LValue, fields: Seq[Record.Field], outBits: Expr, hash: SymLike): LoAst = {
    val mult = (hash := hash * Cast(Const(z), UInt64()))

    val doHash = if (fields.nonEmpty) {
        var shift = 0
        val hashes = for ((f, i) <- fields.zipWithIndex) yield {
          val width = f.loType.widthBytes * 8
          val field = f.name.map(Field(rec, _)).getOrElse(UField(rec, i))
          val fieldHash = (hash := (hash << width) + Cast(field, UInt64()))
          if (shift + width > 64) {
            shift = 0
            mult + fieldHash
          } else {
            shift += width
            fieldHash
          }
        }
        Block(hashes.toList)
    } else {
      (hash := rec)
    }

    DecAssign(hash, UInt64(), 0) +
        doHash +
        mult +
        (hash := hash >> (Const(64) - outBits))
  }
}

object Hash64Generator {

  private val z = 6542915301859449791l

  def multHashStatic(l: Long, outBits: Int): Long = {
    ((EInt(l, 8, false) * EInt(z, 8, false)) >> EInt(64 - outBits, 8, false)).i
  }
  def multHashStatic(l: Seq[(Long, Int)], outBits: Int): Long = {
    var h = EInt(0, 8, false)
    var shift = 0
    for ((n, w) <- l) {
      if (shift + w > 64) {
        shift = 0
        h *= EInt(z, 8, false)
      } else {
        shift += w
      }
      h <<= EInt(w, 8, false)
      h += EInt(n, 8, false)
    }
    h *= EInt(z, 8, false)
    (h >> EInt(64 - outBits, 8, false)).i
  }
}
