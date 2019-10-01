package ressort.hi.compiler
import ressort.lo
import ressort.hi
import ressort.util._
import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen
import org.scalatest.matchers.ShouldMatchers
import scala.collection.mutable.Stack
import scala.collection.mutable.HashMap


class ArrayAllocatorTester extends FunSpec with GivenWhenThen {
  val arr1 = {
    import hi._
    val baseName = Id("A1")

    val innerHist = {
      FlatArray(
        new Buffer(name = lo.Id("buf"), recType = lo.Index(), length = lo.Pow2(lo.Const(4))))
    }

    val inner = {
      HistSlicedArray(
        base =
            FlatArray(
              new Buffer(name = lo.Id("inner_base"), recType = lo.UInt32(), length = lo.Const(1024))),
        hist = innerHist)
    }

    val outerHist = {
      SlicedArray(
        base =
            FlatArray(
              new Buffer(name = lo.Id("outer_hist_base"), recType = lo.Index(), length = lo.Pow2(lo.Const(3)))),
        slices = lo.Const(8),
        parallel = true)
    }

    val outer = {
        HistSlicedArray(
          base = inner,
          hist = outerHist)
    }
    outer
  }
  
  val tids = new lo.TempIds("T_")

  def loDag(harr: MetaArray): LoDag = {
    implicit val env = Map[hi.Id, hi.HiType]()
    val fakeNode =
      new HiDag(
        HiArrayOp(
          hi.TypedHiResOp(
            hi.DagOp(),
            hi.Func(Map(), hi.HiResInt),
            Nil),
          Nil,
          Nil),
        Nil,
        harr,
        Nil)
    LoDag(fakeNode, tids)
  }

  describe("Translation to an ArrayView") {
    Given("an Hi array:\n"+indent(arr1.toString, 3))
    val loArr = loDag(arr1).output
    Then("That should yield an lo array:\n"+indent(loArr.toString, 3))
  }
  
  
  describe("Allocation") {
    val loDag1 = loDag(arr1)
    val alloc = loDag1.allocation
    val loArr = loDag1.output
    Given("an Lo array:\n"+indent(loArr.toString, 3))
    Then("That should produce an allocation Op:\n"+alloc.tabStr(3))
    val top = lo.TypedLoAst(alloc)
    And("That should type-check")
  }
}
