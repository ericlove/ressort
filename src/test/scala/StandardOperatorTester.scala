// See LICENSE.txt
package ressort.top
import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen
import org.scalatest.matchers.ShouldMatchers
import ressort.compiler._
import ressort.lo.interp._
import ressort.hi
import ressort.util._

/** Tests canonical operators (just a placeholder now) */
trait StandardOperatorTester { self: FunSpec with GivenWhenThen =>
  def makeSortTest(
      op: hi.Operator,
      name: String,
      size: Int,
      maxKey: Int,
      trials: Int) {
    println(s"\n\n######### $name #########")
    Then("That should evaluate")
  }
  
  def makePartitionTest(
      op: hi.Operator,
      name: String,
      bits: (Int, Int),
      size: Int,
      maxKey: Int,
      trials: Int) {
    println(s"######### $name #########")
    Then("That should evaluate")
  }

  def makeSelectLessThanTest(
      op: hi.Operator,
      name: String,
      size: Int,
      lessThan: Int,
      maxKey: Int,
      trials: Int) {
    println(s"######### $name #########")
    Then("That should evalute")

  }
      
}
