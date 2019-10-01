// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._
import ressort.util._
import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen
import org.scalatest.matchers.ShouldMatchers
import scala.collection.mutable.Stack

class DeadCodeEliminatorSpec extends FunSpec with LoResTester with GivenWhenThen {
  describe("Dead Code Elimination") {
    it("should eliminate entire blocks with no output") {
      val code = bigDecBlock + bigBoundForLoop //+ ifElse
      Given("Code:\n"+code.tabStr(3))
      val ta = TypedLoAst(code)
      val newAst = DeadCodeEliminator(ta)
      Then("It should produce a new AST:\n"+newAst.ast.tabStr(3))
      assert(newAst.ast === Nop)
      And("It should be empty.")
    }

    it("should not eliminate code that is seen by a return") {
      val code = funcRet
      Given("Code:\n"+code.tabStr(3))
      val ta = TypedLoAst(code)
      val newAst = DeadCodeEliminator(ta)
      Then("It should produce a new AST:\n"+newAst.ast.tabStr(3))
      assert(newAst.ast === code)
      And("That AST should be the same as the original input")
    } 

    it("should selectively eliminate dead code inside a function") {
      val code = funcRetDeadCode 
      Given("Code:\n"+code.tabStr(3))
      val ta = TypedLoAst(code)
      val newAst = DeadCodeEliminator(ta)
      Then("It should produce a new AST:\n"+newAst.ast.tabStr(3))
    }

    it("should eliminate adjacent duplicate definitions") {
      val code = {
        FuncDec(i, List(),
          bigDecBlock + bigDecBlock +
          Return(a + b + c + d),
          Some(Index()))
      }
      Given("Code:\n"+code.tabStr(3))
      val ta = TypedLoAst(code)
      val newAst = DeadCodeEliminator(ta)
      Then("It should produce a new AST:\n"+newAst.ast.tabStr(3))
    }
  }
}
