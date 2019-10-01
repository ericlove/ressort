// See LICENSE.txt
/** LibHiRes: A set of library routines for building complex HiRes operators */
package ressort.hi
import ressort.lo
import ressort.hi._

object SumFloat {
  def apply(o: Operator): Operator = {
    Reduce(o, PlusOp, Some(FloatConst(0.toFloat)))
  }
}

object NestedSumFloat {
  def apply(o: Operator): Operator = {
    NestedReduce(o, PlusOp, Some(FloatConst(0.toFloat)))
  }
}

object SumDouble {
  def apply(o: Operator): Operator = {
    Reduce(o, PlusOp, Some(DoubleConst(0.toDouble)))
  }
}

object NestedSumDouble {
  def apply(o: Operator): Operator = {
    NestedReduce(o, PlusOp, Some(DoubleConst(0.toDouble)))
  }
}

object Count {
  def apply(o: Operator): Operator = {
    Reduce(o(Cast(Const(1), lo.Index())), PlusOp, Some(Const(0)))
  }
}

object Shell {
  def apply(o: Operator): Operator = SplitPar(o, 0)
}


object HistRadixPart {
  def apply(
      input:        Operator,
      key:          FieldName,
      msb:          Expr,
      lsb:          Expr,
      hash:         Operator=>Operator=(o => o),
      parallel:     Boolean=false): Operator = {
  println(s"MSB $msb - LSB $lsb")
    val hist = Histogram(keys = hash(input(key))(BitRange(UField(0), msb, lsb)), slices = (Pow2(msb + 1 - lsb)))
    
    val part =
      Partition(
        keys = hash(input(key))(BitRange(UField(0), msb, lsb)),
        values = input,
        hist = Offsets(hist, depth = (if (parallel) 1 else 0)),
        parallel = parallel)

    Let(
      Seq(
        ('part := part),
        ('values := Uncat('part, 0)),
        ('hist := Uncat('part, 1))),
      in =
        RestoreHistogram(
          'values,
          if (parallel) LastArray('hist) else 'hist)
    )
  }

  /** This is a legacy operator from a previous version of HiRes */
  def apply(o: Operator, bits: Expr): Operator = {
    HistRadixPart(
      input   = o,
      key     = UFieldName(0),
      msb     = Const(31),
      lsb     = Const(32) - bits)
  }
}


/***
  *
  * TODO: Need to come up with a way to make `LsbRadixSort` feasible once more.
  * The old skeleton requires, essentially, intimate knowledge of input records'
  * field structure:
object LsbRadixSort {
  def apply(
      getKey:       Operator => Operator,
      values:       Operator,
      msb:          Int,
      lsb:          Int,
      radix:        Int,
      threads:      Int,
      histPadding:  Int): Operator = {
    val bits = msb - lsb + 1
    val rem = bits % radix
    
    val first = if (rem != 0) {
      Flatten(
        HistRadixPart(
          getKey, values, lsb = Const(lsb), msb = Const(lsb + rem), threads = threads))
    } else {
      values
    }

    def part(base: Operator, lsb: Int): Operator = {
      if (lsb < msb) {
        val partOp = {
          Flatten(
            HistRadixPart(
              getKey  = getKey,
              values  = base,
              lsb     = Const(lsb), 
              msb     = Const(lsb+radix-1),
              threads = threads))
        }
        part(partOp, lsb+radix)
      } else {
        base
      }
    }

    part(first, lsb+rem)
  }
}
***/
