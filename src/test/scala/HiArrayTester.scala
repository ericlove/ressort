// See LICENSE.txt
package ressort.hi.compiler
import ressort.lo
import ressort.hi._
import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen
import org.scalatest.matchers.ShouldMatchers
import scala.collection.mutable.Stack
import scala.collection.mutable.HashMap


class MetaArrayTester extends FunSpec with GivenWhenThen {
  val baseName = lo.Id("A1")
  val arr1 = {
    val baseBase =
      FlatArray(
        new Buffer(name = baseName, recType = lo.UInt32(), length = lo.Const(1024)))

    val base = 
      SlicedArray(base = baseBase, slices = lo.Const(8), parallel = true)

    val hist =
      FlatArray(
        new Buffer(name = lo.Id("hist"), recType = lo.Index(), length = lo.Pow2(lo.Const(8))))

    val hp = HistSlicedArray(base = base, hist = hist)

    hp
  }
  
  describe("Array Nesting and Naming") {
    Given("a nested HiArray "+arr1)
    Then("it should have an appropriately nested name: "+arr1.buffer.name)
    val nested = arr1.asNestedArray.get
    assert(
      nested.ancillaries != Nil,
      "The ancillary list should not be empty in "+nested.ancillaries)
    And("it should have a non-empty ancillary list: "+nested.ancillaries)
  }
}
