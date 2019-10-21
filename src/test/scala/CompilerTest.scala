// See LICENSE.txt
package ressort.example
import ressort.Ressort
import ressort.hi._
import ressort.hi.compiler.OpDag
import ressort.lo.interp.LoInterp
import ressort.lo
import ressort.lo.TempIds
import ressort.util
import ressort.lo.Symtab
import org.scalatest.{FunSpec, GivenWhenThen, fixture}
import ressort.hi.compiler.{HiResCompiler, Hash64Generator}
import ressort.lo.compiler.{LoResCompiler, SplitLoRes}
import scala.collection.mutable.{HashMap, ArrayBuffer}

object CompilerTest {
  val tpch = new TpchSchema.Generator(scale = 0.01.toFloat)
  val smallTpch = new TpchSchema.Generator(scale = 0.0001.toFloat)
  val lbits = List(util.log2Up(tpch.partSize) - 8, 1).max

  lazy val cornerTests =
    List(
      new FunkySquareSum(),
      new Cycle())

  lazy val queryTests =
    List(
      new Scan32(slices = 0),
      new Scan32(slices = 16),
      new Htbl1(tpch),
      new Htbl2(tpch),
      new Htbl3(tpch),
      new Htbl4(tpch),
      new HJoin1(smallTpch),
      new HJoin2(smallTpch),
      new HJoinMulti(smallTpch),
      new HJoinMulti(smallTpch, weave=true),
      new HJoin3(smallTpch),
      new HJoin4(smallTpch),
      new Part1(smallTpch),
      new Part1(smallTpch, threads=16),
      new PartDisjoint(tpch),
      new PartDisjoint(tpch, threads=16))

  lazy val q17tests =
    List(
      new TpchQ17(tpch))

  lazy val q19tests =
    List(
      new TpchQ19AutoNopa(Some(tpch)),
      new TpchQ19Nopa(Some(tpch)),
      new TpchQ19PartAll(Some(tpch), nbits=lbits, earlyMat=false),
      new TpchQ19PartSingle(Some(tpch), nbits=lbits, blockLitem=false),
      new TpchQ19PartSingle(Some(tpch), nbits=lbits, blockLitem=true),
      new TpchQ19PartSingle(Some(tpch), nbits=lbits, blockLitem=true, threads=10),
      new TpchQ19PartAll(Some(tpch), nbits=lbits, earlyMat=true))

  lazy val q19nopaTests = {
    val tf = List(true, false)
    val threadList = List(0, 12)
    for {
      threads <- threadList
      cat <- tf
      useHash <- tf
      compact <- tf
      earlyMat <- tf
      buildPartitioned <- tf
      inline <- tf
      slots <- List(1,4)
    } yield {
      val ehb = if (useHash) Some(0) else None
      new TpchQ19Nopa(
        Some(tpch),
        threads=threads,
        cat=cat,
        extraHashBits=ehb,
        compact=compact,
        earlyMat=earlyMat,
        buildPartitioned=buildPartitioned,
        slots=slots)
    }
  }

  lazy val q19partAllTests = {
    val tf = List(true, false)
    val threadList = List(0, 12)
    for {
      threads <- threadList
      useHash <- tf
      compact <- tf
      earlyMat <- tf
      earlyMatPart <- tf
      buildPartitioned <- tf
      inline <- tf
      slots <- List(4)
    } yield {
      val ehb = if (useHash) Some(0) else None
      new TpchQ19PartAll(
        Some(tpch),
        nbits=6,
        threads=threads,
        extraHashBits=ehb,
        slots=slots,
        compact=compact,
        earlyMatPart=earlyMatPart,
        earlyMat=earlyMat,
        buildPartitioned=buildPartitioned,
        inline=inline)
    }
  }

  lazy val q06tests =
    List(
      new TpchQ06(threads=1, crack=false, tpch=Some(tpch)),
      new TpchQ06(threads=1, crack=true, tpch=Some(tpch)))

  lazy val q01tests = List(new TpchQ01(tpch))

  lazy val tpchTests = 
    q19tests ++ q01tests ++ q06tests ++ q17tests

  lazy val allTests = cornerTests ++ queryTests ++ tpchTests
}

class AllTests extends CompilerTest(CompilerTest.allTests)
class AllCornerTests extends CompilerTest(CompilerTest.cornerTests)
class AllQueryTests extends CompilerTest(CompilerTest.queryTests)

class TpchQ01Test extends CompilerTest(new TpchQ01(CompilerTest.tpch) :: Nil) 
class TpchQ06Test extends CompilerTest(new TpchQ06(threads=16, crack=false, tpch=Some(CompilerTest.tpch)) :: Nil)
class TpchQ06CrackTest extends CompilerTest(new TpchQ06(threads=1, crack=true, tpch=Some(CompilerTest.tpch)) :: Nil)
class TpchQ06CollectTest extends CompilerTest(new TpchQ06(threads=8, crack=true, collect=true, tpch=Some(CompilerTest.tpch)) :: Nil)

class TpchQ17Test extends CompilerTest(new TpchQ17(CompilerTest.smallTpch) :: Nil)

class TpchQ19NopaTest extends CompilerTest(new TpchQ19Nopa(Some(CompilerTest.tpch)) ::Nil)
class AllTpchQ19NopaTests extends CompilerTest(CompilerTest.q19nopaTests)
class TpchQ19PartAllTest extends CompilerTest(new TpchQ19PartAll(Some(CompilerTest.tpch), nbits=CompilerTest.lbits) :: Nil)
class TpchQ19PartSingleTest extends CompilerTest(new TpchQ19PartSingle(Some(CompilerTest.tpch), nbits=CompilerTest.lbits) :: Nil)
class TpchQ19PartSingleThreadTest extends CompilerTest(new TpchQ19PartSingle(Some(CompilerTest.tpch), nbits=CompilerTest.lbits, threads=16) :: Nil)
class TpchQ19PartSingleBlockTest extends CompilerTest(new TpchQ19PartSingle(Some(CompilerTest.tpch), nbits=CompilerTest.lbits, blockLitem=true) :: Nil)
class TpchQ19PartAllEmTest extends CompilerTest(new TpchQ19PartAll(Some(CompilerTest.tpch), nbits=CompilerTest.lbits, earlyMat=true) :: Nil)
class AllTpchQ19PartAllTests extends CompilerTest(CompilerTest.q19partAllTests)
class TpchQ19AutoNopaTest extends CompilerTest(new TpchQ19AutoNopa(Some(CompilerTest.tpch)) :: Nil)
class TpchQ19AutoPartAllTest extends CompilerTest(new TpchQ19AutoPartAll(Some(CompilerTest.tpch), partBits=CompilerTest.lbits) :: Nil)
class TpchQ19SimpleTest extends CompilerTest(new TpchQ19Simple(Some(CompilerTest.tpch)) :: Nil)
class TpchQ19Tests extends CompilerTest(CompilerTest.q19tests)

class Htbl1Test extends CompilerTest(new Htbl1(CompilerTest.tpch) :: Nil)
class Htbl2Test extends CompilerTest(new Htbl2(CompilerTest.tpch) :: Nil)
class Htbl3Test extends CompilerTest(new Htbl3(CompilerTest.tpch) :: Nil)
class Htbl4Test extends CompilerTest(new Htbl4(CompilerTest.tpch) :: Nil)

class HJoin1Test extends CompilerTest(new HJoin1(CompilerTest.smallTpch) :: Nil)
class HJoin2Test extends CompilerTest(new HJoin2(CompilerTest.smallTpch) :: Nil)
class HJoin3Test extends CompilerTest(new HJoin3(CompilerTest.smallTpch) :: Nil)
class HJoin4Test extends CompilerTest(new HJoin4(CompilerTest.smallTpch) :: Nil)
class HJoin5Test extends CompilerTest(new HJoin5(CompilerTest.smallTpch) :: Nil)
class HJoinMultiTest extends CompilerTest(new HJoinMulti(CompilerTest.smallTpch) :: Nil)
class HJoinMultiWeaveTest extends CompilerTest(new HJoinMulti(CompilerTest.smallTpch, weave=true) :: Nil)

class Part1Test extends CompilerTest(new Part1(CompilerTest.smallTpch) :: Nil)
class Part1ThreadTest extends CompilerTest(new Part1(CompilerTest.smallTpch, threads=16) :: Nil)
class PartDisjointTest extends CompilerTest(new PartDisjoint(CompilerTest.smallTpch) :: Nil)
class PartDisjointThreadTest extends CompilerTest(new PartDisjoint(CompilerTest.smallTpch, threads=10) :: Nil)

class Scan32Test extends CompilerTest(new Scan32(slices = 0) :: Nil)
class Scan32ThreadTest extends CompilerTest(new Scan32(slices = 16) :: Nil)
class Scan32IndexIntTest extends CompilerTest(new Scan32IndexInt() :: Nil)

/** Executes a set of [[HiResTest]]s when inherited from
  *
  * This building block is used to construct various named tests intended to be executed
  * from the `sbt` shell via the `testOnly` command during debugging sessions, or sets
  * thereof.  For example `testOnly ressort.example.AllCornerTests` will run all the small
  * compilation unit tests.
  */
abstract class CompilerTest(tests: Seq[HiResTest]) extends fixture.FunSpec with GivenWhenThen {
  case class FixtureParam(verbose: Boolean, debugFuse: Boolean, debugSym: Boolean, debugCpp: Boolean)
  def withFixture(test: OneArgTest) = {
    def getBool(name: String): Boolean = {
      test.configMap.getOptional[String](name) match {
        case Some("true") => true
        case _ => false
      }
    }

    val fixture = FixtureParam(
      debugCpp = getBool("debugCpp"),
      verbose = getBool("verbose"),
      debugFuse = getBool("debugFuse"),
      debugSym = getBool("debugSym"))

    type FixtureParam = fixture.type
    val origDebugSyms = TempIds.debug
    val origDebugFuse = OpDag.debug
    try {
      TempIds.debug = fixture.debugSym
      OpDag.debug = fixture.debugFuse
      withFixture(test.toNoArgTest(fixture))
    } finally {
      TempIds.debug = origDebugSyms
      OpDag.debug = origDebugFuse
    }
  }
  def doTest(test: HiResTest) {
    it(s"Should compile ${test.name}") { fixture =>
      for (n <- 1 to 1) {
        val fc = new HiResCompiler()
        val lc = new LoResCompiler()
        val input = test.input
        Given("HiResCode:\n" + test.hiRes.listing(0, OperatorListing.lineLength).string)
        val clr = fc.compile(test.hiRes, test.funcType, fixture.verbose, Some(test.name))
        val HiResCompiler.CompiledLoRes(hi, hiType, loFunc, defs) = clr
        //println(loFunc.tabStr(2))
          
        Then("That should compile")
        if (fixture.debugCpp) {
          val cpp = {
            val comp = new LoResCompiler()
            val code = comp.translate(clr)
            code.defs
          }
          And("It should produce C++ code:\n"+cpp)
        }
        val call = {
          // All params should have vars of same name in scope (from tpch`)
          lo.Dec('result, loFunc.returnType.get) +
              lo.AssignReturn('result, lo.App(loFunc.name, loFunc.params.map(p => p._1 -> p._1)))
        }
        test.check map { check =>
          val finish = lo.IfElse('flag, lo.Printf("PASS"), lo.Printf("FAIL"))
          val testCode = {
            val s = SplitLoRes(defs + loFunc + input + call + lo.DecAssign('flag, lo.Bool(), lo.True) + check + finish)
            val res = s.defs + s.code
            //println(res.tabStr(2))
            res
          }
          val finalLoRes = {
            val postTrans = lc.applyTransforms(lo.TypedLoAst(testCode))
            val res = LoInterp.ufieldsOnly(postTrans)
            res
          }
          And(s"It should produce LoRes code:\n${finalLoRes.ast.tabStr(3)}")
          val env = {
            val ctx = new LoInterp()
            ctx.eval(finalLoRes)
            ctx
          }
          And(s"It should execute:\n${util.indent(env.consoleLog(), 3)}\n")
          assert(env.valueOf('flag, finalLoRes.scope) == lo.interp.EBool(true))
          And("It should produce the correct result")
        }
        if (test.check.isEmpty) {
          val ensemble = defs + loFunc
          val testCode = {
            val s = SplitLoRes(defs + loFunc)
            val res = s.defs + s.code
            res
          }
          val xform = lc.applyTransforms(lo.TypedLoAst(testCode)).ast
          And(s"It should produce LoRes code:\n${xform.tabStr(3)}")
        }
      }
    }
  }

  tests.map(doTest)
}




///
///
/// Test definitions
///
///


class FunkySquareSumTest extends CompilerTest(new FunkySquareSum(false) :: Nil)

class Cycle extends HiResTest {
  val name = "Cycle"
  val hiRes = {
    Let(
      Seq(
        ('litem := 'lineitem),
        ('la := Block('litem)),
        ('lb := Block('litem)),
        ('a := 'la('l_partkey + Cast(1, lo.UInt()))),
        ('b := 'lb('l_partkey - Cast(1, lo.UInt()))),
        ('aproj := Project('a, 'b)(UField(0))),
        ('bproj := Project('b, Block('a))(UField(0)))
      ),
      in = Project('aproj, Block('bproj))(UField(0) + UField(1))
    )
  }
  val input = lo.Nop
  val funcType = Func(Map('lineitem -> TpchSchema.lineitem), Vec(lo.UInt()))
}

class Position extends HiResTest {
  val hiRes = {
    Let(
      Seq(
        'split1 := SplitPar('lineitem, 8),
        'split2 := SplitSeq('split1, 32)
      ),
      in = Flatten(Flatten(Project('split2('l_partkey), Position('split2))))
    )
  }
  val funcType = Func(Map('lineitem -> TpchSchema.lineitem), Vec(lo.Record(lo.UInt(), lo.Index())))
  val name = "position"
  val input = lo.Nop
}

class Hasher extends HiResTest {
  val hiRes = {
    Hash64('lineitem, 12)
  }
  val funcType = Func(Map('lineitem -> TpchSchema.lineitem), Vec(Payload(lo.UInt16())))
  val input = lo.Nop
  val name = "hasher"
}

class Htbl1(tpch: TpchSchema.Generator) extends HiResTest {
  def input = tpch.allocate
  def name = "Htbl1"
  val hiRes = {
    Let(
        List(
          ('key := 'lineitem('l_quantity)),
          ('ht :=
            HashTable(
              'key,
              hash = Some(Hash64('key, bits=2)),
              buckets = Some(Const(4)),
              slots = Some(Const(2)),
              inlineCounter = true)),
            'hist := Offsets('ht)
          ),
        Flatten(Compact('ht, hist=Some('hist)))
      )
  }

  override val check = {
    val hmap = HashMap[Long, List[Long]]()
    for (i <- 0 until tpch.litemSize) {
      val qty = tpch.l_quantity(i)
      val hash = Hash64Generator.multHashStatic(qty, 2)
      val init = hmap.getOrElse(hash, List())
      if (!init.contains(qty))
        hmap(hash) = qty :: init
    }
    val correct = hmap.keys.toArray.sortBy(n=>n).map(hmap).map(_.reverse).flatten.map(_.toFloat)
    Some(HiResTest.checkArrFloat(correct, lo.Deref(lo.Deref('result).dot('arr))))
  }

  val funcType = Func(Map('lineitem -> TpchSchema.lineitem), Vec(Payload(lo.UInt8())))
}

class Htbl2(tpch: TpchSchema.Generator, inline: Boolean=true) extends HiResTest {
  def input = tpch.allocate
  def name = "Htbl2"

  val hiRes = {
    Let(
      List(
        ('key := 'lineitem('l_quantity)),
        ('ht :=
            HashTable(
              'key,
              hash = Some(Hash64('key, bits=2)),
              buckets = Some(Const(4)),
              slots = Some(Const(2)),
              inlineCounter = inline)),
        'hist := Offsets('ht)
      ),
      Flatten(Compact(Block('ht(UField(0) + 1)), hist=Some('hist)))
    )
  }

  override val check = {
    val hmap = HashMap[Long, List[Long]]()
    for (i <- 0 until tpch.litemSize) {
      val qty = tpch.l_quantity(i)
      val hash = Hash64Generator.multHashStatic(qty, 2)
      val init = hmap.getOrElse(hash, List())
      if (!init.contains(qty + 1))
        hmap(hash) = (qty + 1) :: init
    }
    val correct = hmap.keys.toArray.sortBy(n=>n).map(hmap).map(_.reverse).flatten.map(_.toFloat)
    Some(HiResTest.checkArrFloat(correct, lo.Deref(lo.Deref('result).dot('arr))))
  }

  val funcType = Func(Map('lineitem -> TpchSchema.lineitem), Vec(Payload(lo.UInt8())))
}

class Htbl3(tpch: TpchSchema.Generator, inline: Boolean=true) extends HiResTest {
  val hiRes = {
    Let(
      List(
        ('zip := 'lineitem.project('key -> 'l_quantity, 'pos -> 'l_shipinstruct)),
        ('ht :=
            HashTable(
              'zip,
              hash = Some(Hash64('zip, bits=5)),
              buckets = Some(Const(32)),
              slots = Some(Const(1)),
              inlineCounter = inline)),
        'hist := (Offsets('ht))
      ),
      Flatten(
        Compact(
          Block('ht, nest=true)
              .apply(UField(0)*51 + UField(1))
              .apply(UField(0) * 5),
          hist=Some('hist)))
    )
  }

  override val check = {
    val hmap = HashMap[Long, List[(Long, Long)]]()
    for (i <- 0 until tpch.litemSize) {
      val qty = tpch.l_quantity(i).toLong
      val sinst = tpch.l_shipinstruct(i).toLong
      val hash = Hash64Generator.multHashStatic(List((qty, 8), (sinst, 8)), 5)
      val init = hmap.getOrElse(hash, List())
      if (!init.contains((qty, sinst))) {
        hmap(hash) = (qty, sinst) :: init
      }
    }
    val correct = hmap.keys.toArray.sortBy(n=>n).map(hmap).map(_.reverse).flatten.map(n => (n._1*51 + n._2).toFloat * 5.0.toFloat)
    Some(HiResTest.checkArrFloat(correct, lo.Deref(lo.Deref('result).dot('arr))))
  }

  val funcType = Func(Map('lineitem -> TpchSchema.lineitem), Vec(Payload(lo.Index())))

  val input = tpch.allocate
  val name = "Htbl3"
}

class Htbl4(tpch: TpchSchema.Generator, inline: Boolean=true) extends HiResTest {
  val hiRes = {
    Let(
      List(
        ('zip := 'lineitem.project('key -> 'l_quantity, 'pos -> 'l_shipinstruct)),
        ('ht :=
            HashTable(
              'zip,
              hash = Some(Hash64('zip, bits=5)),
              buckets = Some(Const(32)),
              slots = Some(Const(1)),
              inlineCounter = true
            )),
        'hist := Offsets('ht),
        'comp := Compact('ht, hist=Some('hist))
      ),
      Flatten(Zip('comp(UField(0)), 'comp(UField(1))))
    )
  }

  override val check = {
    val hmap = HashMap[Long, List[(Long, Long)]]()
    for (i <- 0 until tpch.litemSize) {
      val qty = tpch.l_quantity(i).toLong
      val sinst = tpch.l_shipinstruct(i).toLong
      val hash = Hash64Generator.multHashStatic(List((qty, 8), (sinst, 8)), 5)
      val init = hmap.getOrElse(hash, List())
      if (!init.contains((qty, sinst))) {
        hmap(hash) = (qty, sinst) :: init
      }
    }
    val correct = hmap.keys.toArray.sortBy(n=>n).map(hmap).map(_.reverse).flatten
    val arr =lo.Deref(lo.Field(lo.Deref('result), 'arr))
    Some(
      HiResTest.checkArrFloat(correct.map(_._1.toFloat), arr, Some(x => lo.UField(x, 0))) +
      HiResTest.checkArrFloat(correct.map(_._2.toFloat), arr, Some(x => lo.UField(x, 1))))
  }

  val funcType = Func(Map('lineitem -> TpchSchema.lineitem), Vec(Payload(lo.Record(lo.Index(), lo.Index()))))
  val input = tpch.allocate
  val name = "Htbl4"
}


class HJoin1(tpch: TpchSchema.Generator) extends HiResTest {
  val bits = 10
  def hash(o: Operator) = Hash64(o, bits)

  def table: Operator = {
    HashTable(
      'part.fields('p_partkey, 'p_retailprice),
      hash = Some(hash('part('p_partkey))),
      buckets = Some(Pow2(bits)))
  }

  def join: Operator = {
    Let(
      List(
        'table := Block(table),
        'litem := 'lineitem.fields('l_partkey, 'l_extendedprice)),
      in = HashJoin('litem, 'table, hash('litem('l_partkey))))
  }

  def hiRes: Operator = {
    Let(
      List(
        'join := join,
        'hist := Offsets('join)),
    Flatten(Compact('join, hist=Some('hist))))
  }

  val name = "HJoin1"

  val input = tpch.allocate
  val funcType =
    Func(
      Map('lineitem -> TpchSchema.lineitem, 'part -> TpchSchema.part),
      Vec(Payload(
        lo.Record(
          lo.Record.Field(lo.UInt32(), Some(lo.Id("l_partkey"))),
          lo.Record.Field(lo.LoFloat(), Some(lo.Id("l_extendedprice"))),
          lo.Record.Field(lo.LoFloat(), Some(lo.Id("p_retailprice")))
        ))))

  override val check = {
    case class Rec(l_partkey: Long, l_extendedprice: Float, p_retailprice: Float)
    val htbl = HashMap[Long, Float]() // For each p_partkey, its p_retailprice
    val out = ArrayBuffer[Rec]()
    for (i <- 0 until tpch.partSize) {
      htbl(tpch.p_partkey(i)) = tpch.p_retailprice(i)
    }
    for (i <- 0 until tpch.litemSize) {
      val pkey = tpch.l_partkey(i)
      out += Rec(pkey, tpch.l_extendedprice(i), htbl(pkey))
    }
    val correct = out.toArray
    val arr = lo.Deref(lo.Field(lo.Deref('result), 'arr))
    Some(
      HiResTest.checkArrLong(correct.map(_.l_partkey), arr, Some(x => lo.Field(x, 'l_partkey))) +
      HiResTest.checkArrFloat(correct.map(_.l_extendedprice), arr, Some(x => lo.Field(x, 'l_extendedprice))) +
      HiResTest.checkArrFloat(correct.map(_.p_retailprice), arr, Some(x => lo.Field(x, 'p_retailprice))))
  }
}

class HJoin2(tpch: TpchSchema.Generator) extends HJoin1(tpch) {
  override def table: Operator = {
    Let(
      List(
        'part := SplitPar('part, 0)),
      Block(HashTable(
        'part.fields('p_partkey, 'p_retailprice),
        hash = Some(hash('part('p_partkey))),
        buckets = Some(Pow2(bits))), nonFusable=true))
  }
  override def hiRes = {
    Let(
      List(
        'lineitem := SplitPar(SplitPar('lineitem, 10), 0)
      ), in = Flatten(super.hiRes))
  }

  override val name = "HJoin2"
}


class HJoin3(tpch: TpchSchema.Generator) extends HJoin1(tpch) {
  override val name = "HJoin3"

  override def table: Operator = {
    HashTable(
      'part.fields('p_partkey).projectWithPosition(),
      hash = Some(hash('part('p_partkey))),
      buckets = Some(Pow2(bits)))
  }

  override def hiRes: Operator = {
    Let(
      List(
        'join := super.hiRes,
        'p_retailprice := Gather('join('position), 'part)('p_retailprice),
        'join := Project('join, 'p_retailprice)),
      in = 'join.project(
        'l_partkey -> 'l_partkey,
        'l_extendedprice -> 'l_extendedprice,
        'p_retailprice -> 'p_retailprice))
  }
}

class HJoin4(tpch: TpchSchema.Generator) extends HJoin1(tpch) {
  override val name = "HJoin4"

  override def table: Operator = {
    HashTable(
      'part.fields('p_partkey).projectWithPosition(),
      hash = Some(hash('part('p_partkey))),
      buckets = Some(Pow2(bits)))
  }


  override def hiRes: Operator = {
    Let(
      List(
        'join := super.join,
        'p_retailprice := Gather('join('position), 'part)('p_retailprice),
        'join := Project('join, 'p_retailprice),
        'join := 'join.project(
          'l_partkey -> 'l_partkey,
          'l_extendedprice -> 'l_extendedprice,
          'p_retailprice -> 'p_retailprice),
        'join := Compact('join, hist=Some(Offsets('join)))),
      in = Flatten('join))
  }
}

class HJoin5(tpch: TpchSchema.Generator) extends HJoin1(tpch) {
  override def table: Operator = {
    Let(
      List(
        'part := Shell(Shell(SplitPar('part, 0)))),
      Block(HashTable(
        'part.fields('p_partkey, 'p_retailprice),
        hash = Some(hash('part('p_partkey))),
        buckets = Some(Pow2(bits))), nonFusable=true))
  }
  override def hiRes = {
    Let(
      List(
        'lineitem := SplitSeq(SplitPar(SplitPar('lineitem, 10), 2), 3)
      ), in = Flatten(Flatten(super.hiRes)))
  }

  override val name = "HJoin5"
}

class HJoinMulti(tpch: TpchSchema.Generator, weave: Boolean=false) extends HiResTest {
  val page = tpch.litemSize / 256

  def hash(o: Operator) = Hash64(o, 10)

  def input = tpch.allocate

  def name = "HJoinMulti" + (if (weave) "_weave" else "")

  def hiRes: Operator = {
    val ltbl = {
      HashTable(
        'lineitem.project(
          'l_partkey -> 'l_partkey,
          'l_quantity -> 'l_quantity),
        hash = Some(hash('lineitem('l_partkey))),
        aggregates = List(('l_quantity, PlusOp)))
    }
    
    val ptbl = {
      HashTable(
        'part.project(
          'p_partkey -> 'p_partkey,
          'p_retailprice -> 'p_retailprice),
        hash = Some(hash('part('p_partkey))))
    }

    Let(
      List(
        'ltbl := ltbl,
        'lineitem := (if (weave) SplitSeq('lineitem, page) else 'lineitem),
        'ljoin :=
          HashJoin(
            left = 'lineitem.project('l_partkey -> 'l_partkey),
            right = 'ltbl,
            hash = hash('lineitem('l_partkey))),
        'ptbl := ptbl,
        'pjoin := HashJoin('ljoin, 'ptbl, hash = hash('ljoin('l_partkey))),
        'cpct := (Flatten(Compact('pjoin, hist = Some(Offsets('pjoin)))))),
      in = 'cpct)
  }

  val funcType = {
    Func(
      Map('lineitem -> TpchSchema.lineitem, 'part -> TpchSchema.part),
      Vec(Payload(
        lo.Record(
          lo.Record.Field(lo.UInt32()),
          lo.Record.Field(lo.UInt32()),
          lo.Record.Field(lo.LoFloat())))))
  }
}

class Part1(tpch: TpchSchema.Generator, nbits: Int=10, threads: Int=1) extends HiResTest {
  val hiRes = {
    Let(List(
      'litem := (if (threads > 1) SplitPar('lineitem, threads) else 'lineitem),
      'hash := Hash64('litem('l_partkey), nbits),
      'rec := Project('hash, 'litem('l_partkey), Position('litem))),
    in = Flatten(HistRadixPart('rec, 0, nbits-1, 0, parallel = threads > 1)))
  }

  val name = s"Part1_t$threads"

  val input = tpch.allocate

  val funcType =
    Func(
      Map('lineitem -> TpchSchema.lineitem),
      Vec(Payload(
        lo.Record(
          lo.Record.Field(lo.UInt64()),
          lo.Record.Field(lo.UInt32()),
          lo.Record.Field(lo.Index())))))

  override val check = {
    case class Rec(hash: Long, partkey: Long, pos: Long)
    val buckets = Array.fill(1 << nbits) { new ArrayBuffer[Rec]() }
    for (i <- 0 until tpch.litemSize) {
      val pkey = tpch.l_partkey(i)
      val part = Hash64Generator.multHashStatic(pkey, nbits)
      buckets(part.toInt) += Rec(part, pkey, i)
    }
    val out = buckets.flatten
    val arr = lo.Deref(lo.Field(lo.Deref('result), 'arr))
    Some(
      HiResTest.checkArrLong(out.map(_.hash), arr, Some(x => lo.UField(x, 0))) + 
      HiResTest.checkArrLong(out.map(_.partkey), arr, Some(x => lo.UField(x, 1))) +
      HiResTest.checkArrLong(out.map(_.pos), arr, Some(x => lo.UField(x, 2))))
  }
}

class PartDisjoint(tpch: TpchSchema.Generator, nbits: Int=3, threads: Int=1) extends Part1(tpch, nbits, threads) {
  override val name = s"PartDisjoint_t$threads"
    override val hiRes = {
      Let(List(
        'litem := (if (threads > 1) SplitPar('lineitem, threads) else 'lineitem),
        'hash := Hash64('litem('l_partkey), nbits),
        'rec := Project('hash, 'litem('l_partkey), Position('litem)),
        'hist := Histogram('hash, slices = Pow2(nbits)),
        'hist := Offsets('hist, depth=(if (threads > 1) 1 else 0), disjoint=true),
        'p := Partition('hash, 'rec, 'hist, disjoint=true, parallel = (threads > 1)),
        'part := Uncat('p, 0),
        'hist := Uncat('p, 1),
        'part := RestoreHistogram('part, (if (threads > 1) LastArray('hist) else 'hist)),
        'off := Offsets('part), 
        'part := Compact('part, hist=Some('off))),
      in = Flatten('part))
  }
}


