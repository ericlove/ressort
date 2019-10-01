package ressort.lo.compiler
import ressort.lo._
import org.scalatest.{FunSpec, GivenWhenThen}

class CseTester extends FunSpec with GivenWhenThen with CseTests {
  cseTests()
}

trait CseTests {
  this: FunSpec with GivenWhenThen =>
  def cseTests() {
    describe("Common Subexpression Elimination") {
      def test(code: LoAst): Unit = {
        val tabs = 0
        Given(s"Code:\n" + code.tabStr(tabs))
        val typed = TypedLoAst(code)
        val ssa = StaticSingleAssignment(typed)
        And(s"Post-SSA form\n" + ssa.ast.tabStr(tabs))
        val cse = (UniqueSymbolNames(CommonSubExpressions(ssa)))
        Then("That should pass CSE:\n" + cse.ast.tabStr(tabs))
        val dce = UniqueSymbolNames(DeadCodeEliminator(CommonSubExpressions(ssa)))
        And("It should survice DCE:\n"+dce.ast.tabStr(tabs))
        val fin =
          UniqueSymbolNames(
            DeadCodeEliminator(
              StaticSingleAssignment.collapse(
                PropagateConstants(
                  CommonSubExpressions(ssa), true)), true))
        And("It should survive SSA collapse:\n" + fin.ast.tabStr(tabs))
      }

      it("Should do simple assignments") {
        val code = {
          DecAssign('x, Index(), Const(10) + Const(10)) +
            DecAssign('y, Index(), Const(10) + Const(10)) +
            DecAssign('z, Index(), 'x + 'y) +
            DecAssign('q, Index(), 'y + 'x)
        }
        test(code)
      }
      it("Should do simple for loops") {
        val code = {
          DecAssign('x, Index(), Const(0)) +
            ForBlock('i, 100, 'x := 'x + 1)
        }
        test(code)
      }
      it("Should do other simple for loops") {
        val code = {
          DecAssign('x, Index(), Const(0)) +
              ForBlock('i, 100,
                    ('x := 'x + 1) +
                        ('y := (Index(), 'x + 1)) +
                        ('z := (Index(), 'x - 1)) +
                        ('a := (Index(), 'x - 1)) +
                        ('x := 'a)) +
              Printf("%d", ('x - 1) - ('x + 1))
        }
        test(code)
      }
      it("Should Handle Nested If-Else Clauses") {
        val code = {
          FuncDec('f, List('x -> Index(), 'a -> Index()),
            ForBlock('i, Const(10),
              ('y := (Index(), Const(0))) +
                ('z := (Index(), 'a + 1)) +
                IfElse('i > 'x, ('y := 'x), ('y := 'y + Const(1)))
            )
          )
        }
        test(code)
      }
      it("Should Handle Other Nested If-Else Clauses") {
        val code = {
          ('x := (Index(), 0)) +
              Dec('y, Index()) +
          ForBlock('z, 10,
            ('x := 'x + 'z) +
            IfElse('x > 0,
              'y := 'x +1,
              'y := 'x-1)
          ) +
          Printf("%d %d", 'y, 'x - 1)
        }
        test(code)
      }

      it("Should handle nested for loops") {
        val code =
          DecAssign('x, Index(), Const(0)) +
            ForBlock('i, 100,
              ('x := 'x + 'i) + ('x := 'x - Const(1)) +
                ForBlock('z, 10, 'x := 'x + 'z) +
                ForBlock('z, 10, 'x := 'x + 'z) +
                ForBlock('z, 10, 'x := 'x - 'z)
            ) +
            DecAssign('y, Index(), 'x * 'x)
        test(code)
      }

      it("Should handle subscripts properly") {
        val code =
          Dec('a, Ptr(Arr(Index()))) +
          HeapAlloc(('a), Some(100)) +
          ForBlock('i, 100, Deref('a).sub('i) := 'i) +
          Assign(Deref('a).sub(1), Const(1)) +
          Printf("%d", Deref('a).sub(0))
        test(code)
      }

      it("Should handle AssignReturn statements") {
        val code = {
          FuncDec('f, List('x -> LoInt()), returnType = Some(LoInt()), body = Return('x + 1)) +
          Dec('y, LoInt()) + AssignReturn('y, App('f, List('x -> Const(1)))) +
          DecAssign('z, LoInt(), 'y + 1)
        }
        test(code)
      }


      it ("Should handle zero-iteration loops") {
        val code = {
          DecAssign('x, Index(), 7) +
          Dec('y, Index()) +
              ForBlock('i, 0, Assign('x, 0) + Assign('y, 'y + 1)) +
              Printf("x = %d, y = %d", 'x, 'y)
        }
        test(code)
      }

      it ("Should handle subscripts inside if statements") {
        val code = {
          Dec('a, Ptr(Arr(Index()))) +
          HeapAlloc('a, Some(10)) +
          ForBlock('i, 10, (Deref('a).sub('i) := 'i * 'i)) +
          DecAssign('b, Index(), 0) +
          DecAssign('c, Index(), 0) +
          ForBlock('i, 10,
            DecAssign('d, Index(), 'i * 'i) +
            IPar('j, 10,
              If(Equal('d % 2, 0),
                DecAssign('d, Index(), Deref('a).sub('i)) +
                (Deref('a).sub('i) := Deref('a).sub('i) + 'd * 'j))) +
            ('b := 'b + 'i)) +
          (Deref('a).sub(0) := 'b) +
          Printf("%d", Deref('a).sub(0))
        }
        test(code)
      }
    }
  }
}
