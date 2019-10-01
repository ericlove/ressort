
package ressort.lo.interp
import ressort.lo._
import ressort.lo.interp._
import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen
import org.scalatest.matchers.ShouldMatchers

class InterpIntSpec extends FunSpec with GivenWhenThen {
  def indent(o: LoAst) = "\n"+o.tabStr(4)+"\n"

  val u8_255  = EInt(255, 1, false)
  val u8_0    = EInt(0, 1, false)
  val u8_1    = EInt(1, 1, false)

  val i8_255  = EInt(255, 1, true)
  val i8_0    = EInt(0, 1, true)
  val i8_1    = EInt(1, 1, true)

  val i16_1   = EInt(1, 2, true)

  val u64_1   = EInt(1, 8, false)

  describe("Handling of 8-bit signed and unsigned integers") {
    it("should correctly overflow") {
      Given(u8_255.toString)

      assert(u8_255 > u8_0)
      Then(s"$u8_255 > $u8_0")
      
      assert(u8_255 > u8_255 + u8_1)
      Then(s"$u8_255 > $u8_255 + $u8_1 = ${u8_255 + u8_1}")

      assert(u8_255 > u8_255 - u8_1)
      Then(s"$u8_255 > $u8_255 - $u8_1 = ${u8_255 - u8_1}")

      Given(i8_255.toString)

      assert(i8_255 < i8_0)
      Then(s"$i8_255 < $i8_0")

      assert(i8_255 < i8_255 + i8_1)
      Then(s"$i8_255 < $i8_255 + $i8_1 = ${i8_255 + i8_1}")
    }

    it("should convert to wider types when appropriate") {
      Given(i16_1.toString)

      assert(u8_255 + i16_1 > u8_255)
      Then(s"$u8_255 + $i16_1 = ${u8_255 + i16_1} > $u8_255")
    }
  }

  describe("A 64-bit integer") {
    it("should be able to be added to another integer correctly") {
      Given(u64_1.toString)

      assert(u64_1 + u64_1 === EInt(2, 8, false))
      Then(s"$u64_1 + $u64_1 = ${u64_1 + u64_1} = 2")
    }
  }
}
