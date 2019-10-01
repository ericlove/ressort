package ressort.example
import ressort._
import ressort.hi
import ressort.lo

class Scan32(val slices: hi.Const) extends HiResTest {
  import hi._
  val input = lo.Nop
  val env = Map[Id, hi.Data](
    'table -> Vec(lo.SplitRecord((lo.UInt32()::Nil), (lo.UInt32()::Nil))),
    'k_upper -> lo.UInt32())

  val hiRes = {
    val table: Operator =  if (slices.n > 0) {
      SplitPar('table, slices)
    } else {
      'table
    }

    Let(Seq(
      ('in := table),
      ('coll :=
          Collect(
            Mask('in, 'in(UField(0) < 'k_upper))))
      ),
      Zip('coll(UField(0)), 'coll(UField(1)))
    )
  }

  val toType = {
    val vec = Vec(lo.SplitRecord((lo.UInt32()::Nil), (lo.UInt32()::Nil)), slices.n == 0)
    if (slices.n > 0) Arr(vec, numValid=true) else vec
  }
  val name = s"scan32_s${slices}"
  val funcType = Func(env, toType)
}

class Scan32IndexInt extends HiResTest {
  import hi._
  val input = lo.Nop

  val hiRes = {
    Let(Seq(
      ('in := 'input),
      ('mask := Mask('in, 'in('value < 'maxval)))
    ),
    Collect(
      'mask.project(
        'key -> 'key,
        'value -> 'value)))
       
  }

  val name = s"scan32indexint"


  val funcType = {
    val inRec = 
      lo.SplitRecord(
        lo.Record.Field(lo.Index(), Some('key)) :: Nil,
        lo.Record.Field(lo.LoInt(), Some('value)) :: Nil)  

    val outRec = lo.FlatRecord(inRec.fields, None)

    Func(
      Map[Id, hi.Data]('input -> Vec(inRec), 'maxval -> lo.LoInt()),
      Vec(outRec, true))
  }
}
