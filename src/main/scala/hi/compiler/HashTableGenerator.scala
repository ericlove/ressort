// See LICENSE.txt
package ressort.hi.compiler

import ressort.hi
import ressort.lo._

case class HashTableGenerator(elaboration: Elaboration) extends CodeGenerator {

  val generatorName = "htbl"

  def emit(
      input: RecParallelIO,
      hash: Option[RecParallelIO],
      output: ChunkArray.ChunkView,
      op: hi.HashTable): LoAst = {

    val recType = input.recType
    val aggFields = op.aggregates.map(_._1)
    val keyFields = HashTableGenerator.keyFields(op, recType)

    val bucket = elaboration.tempIds.newId("bkt")
    val setBucket = hash match {
      case Some(h) => (bucket := (Index(), h.currentRec))
      case None => {
        val gen = new Hash64Generator(elaboration)
        val hashSym = elaboration.tempIds.newId("hash")
        val buckets = output.base.numArrays
        gen.multHash(input.currentRec, keyFields.map(_._1), Log2Up(buckets-1), hashSym) +
            (bucket := (Index(), hashSym % buckets))
      }
    }

    def compareFields(inRec: LValue, probeRec: LValue): Expr = {
      val comps = keyFields.map(_._2).map(idx => Equal(UField(probeRec, idx), UField(inRec, idx)))
      if (comps.nonEmpty)
        comps.foldLeft[Expr](True)(And(_, _))
      else if (aggFields.isEmpty)
        Equal(inRec, probeRec)
      else
        True
    }

    val found = elaboration.tempIds.newId("found")
    val i = elaboration.tempIds.newId("i")
    val j = elaboration.tempIds.newId("j")
    val inRec = elaboration.tempIds.newId("in")
    val aggregate = {
      val aggs = for ((f, aop) <- op.aggregates) yield {
        val (inField, outField) = f match {
          case hi.UFieldName(i) => (UField(inRec, i), UField(output.access(j), i))
          case hi.NFieldName(i) => (Field(inRec, Id(i.name)), Field(output.access(j), Id(i.name)))
        }
        val applyOp = aop match {
          case hi.PlusOp => inField + outField
          case hi.MulOp => inField * outField
          case hi.MinOp => Mux(inField < outField, inField, outField)
          case hi.MaxOp => Mux(inField > outField, inField, outField)
          case hi.AndOp => inField && outField
          case hi.OrOp => inField || outField
        }
        Assign(outField, applyOp)
      }
      Block(aggs.toList)
    }
    val findMatch =
      DecAssign(found, Bool(), False) +
      DecAssign(inRec, input.recType, input.currentRec) +
      output.resetLocalState +
      //Printf("Find %d in b %d [ct %d, cs %d]:", inRec, bucket, output.state.count, output.state.chunkSize) +
      ForBlock(i, output.numArrays,
        If(Not(found),
          //Printf("\tChunk %d [%d slots]:", i, output.maxCursor) +
              ForBlock(j, output.maxCursor,
                    If(compareFields(inRec, output.access(j)),
                          (found := True) + aggregate //+
                              //Printf("\t\tComp %d to %d [s %d]: found = %b", inRec, output.access(j), j, found)
                    ) +
                    If(Not(found),
                     // Printf("\t\tComp %d to %d : found = %b", inRec, output.access(j), found) +
                      Nop
                        )
              ) +
              If(Not(found), output.nonAllocIncrement)
        )
      ) +
    If(Not(found),
      DecAssign('old, Index(), output.state.maxSlot) +
      (output.append) +
          //Printf("New max slot: %d from old %d", output.state.maxSlot, 'old) +
          //Printf(s"\tAppend %d at buck %d[c%d - s%d]",
            //inRec, bucket, output.state.numArrays-1, output.state.maxSlot-1) +
          (output.access(output.maxCursor-1) := inRec)
    )

    output.base.globalState +
        setBucket +
        output.base.localState(bucket) +
        output.globalState +
        findMatch
  }
}

object HashTableGenerator {
  def keyFields(op: hi.HashTable, recType: Scalar): Seq[(Record.Field, Int)] = {
    val aggFields = op.aggregates.map(_._1)
    val excludedIndices = aggFields.filter(_.isInstanceOf[hi.UFieldName]).map(_.asInstanceOf[hi.UFieldName].i)
    val excludedNames = aggFields.filter(_.isInstanceOf[hi.NFieldName]).map(_.asInstanceOf[hi.NFieldName].i.name)
    recType match {
      case r: Record =>
        r.fields.zipWithIndex
            .filter(f => !excludedIndices.contains(f._2))
            .filter(f => !f._1.name.map(n => excludedNames.contains(n.name)).getOrElse(true))
      case _ => List()
    }
  }

  def keyWidthBits(op: hi.HashTable, recType: Scalar): Int = {
    val fields = keyFields(op, recType)
    fields.map(_._1.loType.widthBytes).sum * 8
  }
}
