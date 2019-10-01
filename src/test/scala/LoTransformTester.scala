package ressort.lo.compiler
import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen
import ressort.lo._
import ressort.lo.interp._

class LoTransformTester extends FunSpec with GivenWhenThen with CseTests {
  val Indent = 3

  def checkEquiv(
      env: LoInterp,
      scope: Symtab,
      lv: LValue, 
      n: Int, 
      loType: IntValued=LoInt()): Unit = {
    assert(env.valueOf(lv, scope).toEInt(None).equiv(EInt(n, loType), None))
    Then(s"id should be equal to EInt($n, $loType)")
  }


  describe("Static Single Assignment Form") {
    def test(code: LoAst): Unit = {
      Given(s"Code:\n" + code.tabStr(3))
      val typed = TypedLoAst(code)
      val ssa = UniqueSymbolNames(StaticSingleAssignment(typed))
      Then(s"that should pass SSA\n" + ssa.ast.tabStr(3))
    }
    it ("Should handle simple decs and assigns") {
      val code =
        DecAssign('x, Index(), Const(0)) +
          Assign('x, 'x + Const(1))
      test(code)
    }
    it ("Should handle for loops") {
      val code =
        DecAssign('x, Index(), Const(0)) +
          ForBlock('i, 100, ('x := 'x + 'i) + ('x := 'x - Const(1))) +
          DecAssign('y, Index(), 'x * 'x)
      test(code)
    }
    it ("Should handle if statements") {
      val code =
        DecAssign('x, Index(), Const(0)) +
        If('x > Const(0), 'x := 'x + Const(1)) +
        IfElse('x < Const(1), 'x := Const(1), 'x := 'x + Const(100)) +
        DecAssign('y, Index(), 'x * 'x + Const(1))
      test(code)
    }

    it ("Should handle nested if statements") {
      val code =
        DecAssign('x, Index(), Const(0)) +
          IfElse('x < 10,
            IfElse('x > 5, 'x := 'x - 1, 'x := 'x + 2),
            'x := 'x + 100) +
        DecAssign('y, Index(), 'x * 'x + 1)
      test(code)

    }

    it ("Should handle nested for loops") {
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

    it ("should handle nests of for and if") {
      val code =
        DecAssign('b, Bool(), False) +
            ForBlock('i, 10,
              If(Not('b),
                ForBlock('j, 10,
                  If(Not('b) && Equal('i * 'j, 70),
                    ('b := True)
                  )
                ))
            )
      test(code)
    }

    it ("should handle more complex nests of for and if") {
      val code =
        DecAssign('b, Bool(), False) +
        Dec('ii, LoInt()) +
        Dec('jj, LoInt()) +
        ForBlock('i, 10,
          If(Not('b),
            ForBlock('j, 10,
              If(Not('b) && Equal('i * 'j, 70),
                ('b := True) +
                    ('ii := 'i) +
                    ('jj := 'j)
                )
            ))
        ) +
      Printf("ii = %d; jj = %d", 'ii, 'jj)
      test(code)
    }

    it ("Should handle zero-iteration loops") {
      val code = {
        DecAssign('x, Index(), 7) +
        ForBlock('i, 0, Assign('x, 0)) +
        Printf("x = %d", 'x)
      }
      test(code)
    }

    it ("Should handle arrays & pointers") {
      val code = {
        Dec('a, Ptr(Arr(Index()))) +
        HeapAlloc('a, Some(10)) +
        Assign(Deref('a).sub(0), 1) +
        ForSeq('i, 1, 10, 1,
          Assign(Deref('a).sub('i), Deref('a).sub('i-1)) +
          Assign(Deref('a).sub(5), 'i) +
          Assign(Deref('a).sub('i), Deref('a).sub('i) + 1))
      }
      test(code)
    }
  }

  cseTests()

  describe("The Function Linearizer") {
    def isLinear(ast: LoAst): Boolean = {
      def isFunc(ast: LoAst): Boolean = ast match {
        case fd: FuncDec => true
        case _ => false
      }
      import ressort.lo.compiler.AstTransform
      object LinTest extends AstTransform {
        case class P(containsFuncs: Boolean, isLinear: Boolean)
        type T = P
        def trans(oldOp: LoAst, children: List[XFormAst]) = {
          val childrenLinear = children.foldLeft(true) {
            (a,b) => a && b.payload.isLinear
          }
          val childFuncsVec = children map { ch => ch.payload.containsFuncs }
          val childFuncs = childFuncsVec.foldLeft(false) {
            (a,b) => a || b
          }
          if(isFunc(oldOp)) {
            XFormAst(oldOp, P(true, !childFuncs && childrenLinear))
          } else {
            XFormAst(oldOp, P(childFuncs, childrenLinear))
          }
        }
      }
      LinTest.dfTrans(ast).payload.isLinear
    }
    val xyarg = Seq[(Id, Primitive)]('x->UInt(), 'y->Ptr(UInt()))
    val f1Dec = FuncDec('f1, xyarg, Deref('y) := 'x*'x)
    val f2Dec = FuncDec('f2, xyarg, Deref('y) := Const(1)-'x)
    val ff2Dec = {
      FuncDec(
        'ff2,
        xyarg,
        f1Dec + 'f1('x -> 'x, 'y->Ref('x)))
    }
    val fff2Dec = {
      FuncDec(
        'fff2,
        xyarg,
        f2Dec + {
          ForBlock(
            'x,
            Const(10), {
              ff2Dec +
              'ff2('x -> 'x, 'y -> Ref('x)) +
              'f2('x -> 'x, 'y -> Ref('x))
          })
        })
    }

    it("Should tell linear from non-linear funcs") {
      Given("Linear funcs: \n"+f1Dec.tabStr(Indent)+"\n"+f2Dec.tabStr(Indent))
      assert(isLinear(f1Dec), "f1 should be linear")
      assert(isLinear(f2Dec), "f2 should be linear")
      TypedLoAst(f1Dec)
      TypedLoAst(f2Dec)
      Then("that should be linear")
      Given("Simple non-linear func: \n"+ff2Dec.tabStr(Indent))
      assert(!isLinear(ff2Dec))
      TypedLoAst(ff2Dec)
      Then("That should be non-linear")
      Given("A multiply-nested non-linear func: \n"+fff2Dec.tabStr(Indent))
      assert(!isLinear(fff2Dec))
      TypedLoAst(fff2Dec)
      Then("That should be non-linear too.")
    }
    it("Should linearize non-linear funcs") {
      Given("A simple non-linear func:\n "+ff2Dec.tabStr(Indent))
      TypedLoAst(ff2Dec)
      val ff2Dec_lin = Linearizer(TypedLoAst(ff2Dec)).ast
      And("Output \n"+ff2Dec_lin.tabStr(Indent))
      assert(isLinear(ff2Dec_lin))
      TypedLoAst(ff2Dec_lin)
      Then("Output:\n"+ff2Dec_lin.tabStr(Indent)+" should be linear.")
      Given("A multiply-nested non-linear func:\n"+fff2Dec.tabStr(Indent))
      val fff2Dec_lin = Linearizer(TypedLoAst(fff2Dec)).ast
      assert(isLinear(fff2Dec_lin))
      TypedLoAst(fff2Dec_lin)
      Then("Output:\n"+fff2Dec_lin.tabStr(Indent)+" should be linear too.")
      Linearizer(TypedLoAst(fff2Dec_lin))
      And("The linearizer should be idempotent")
    }
    it("Should not place new FuncDecs before Typedefs or other FuncDecs they depend on.") {
      val Z = Struct('z, List('y -> LoInt(), 'q -> LoInt()))
      val testCode = {
        Typedef(Z) +
        FuncDec('f1, List('x -> Ptr(LoInt())), Deref('x) := Deref('x) - Const(1)) +
        FuncDec('f2, List('x -> Ptr(Z)),
          FuncDec('f3, List('x -> Ptr(Z)),
            Dec('q, TypeRef('z)) +
            ('q.dot('y) := Const(12)) +
            'f1('x -> Ref(Deref('x).dot('q)))) +
          App('f3, List('x -> 'x)) +
          App('f1, List('x -> Ref(Deref('x).dot('q))))) +
        Dec('q, Z) +
        ('z.dot('q) := Const(5)) +
        ('z.dot('y) := Const(7)) +
        App('f2, List('x -> Ref('z)))
      }
      Given("Code:\n"+testCode.tabStr(3))
      val top = TypedLoAst(testCode)
      Then("That code should type check.")
      val linearized = Linearizer(top)
      assert(isLinear(linearized.ast))
      And("That should linearize:\n"+linearized.ast.tabStr(3))
    }
    it("Should not miss AssignReturn statements.") {
      val Z = Struct('z, List('y -> LoInt(), 'q -> LoInt()))
      val testCode = {
        FuncDec('f2, List('x -> LoInt()),
          Dec('y, Ptr(LoInt())) +
          HeapAlloc('y) +
          (Deref('y) := 'x) +
          Return('y),
          Some(Ptr(LoInt()))) +
        FuncDec('f1, List('x -> LoInt()),
          FuncDec('f2, List('y -> LoInt()),
            Return('y * 10),
            Some(LoInt())) +
          Dec('y, LoInt()) +
          AssignReturn('y, 'f2('y -> 'y)) +
          Return('x * 'y + 1),
          Some(LoInt())) +
        Dec('y, Ptr(LoInt())) +
        AssignReturn('y, 'f2('x -> 1)) +
        AssignReturn(Deref('y), 'f1('x -> 10))
      }
      Given("Code:\n"+testCode.tabStr(3))
      val top = TypedLoAst(testCode)
      Then("That should typecheck")
      val lin = Linearizer(top)
      assert(isLinear(lin.ast))
      And("It should linearlize:\n"+lin.ast.tabStr(3))
    }

  }


  describe("The ArrayStruct transform") {
    val simpleDec = Dec('a, Ptr(Arr((LoInt())))) + HeapAlloc('a, Some(100))
    val simpleAssign = Subsc(Deref('a), Const(0)) := Const(777)
    val nestAssign = {
      (Subsc(Subsc(Deref('a), Const(0)), Const(1)) := Const(888)) +
      DecAssign('x, Ptr(LoInt()), Ref(Deref('a).sub(Const(0)).sub(Const(1)))) +
      DecAssign('y, Ptr(Arr(LoInt())), Ref(Deref('a).sub(Const(0)))) +
      DecAssign('z, LoInt(), Deref('y).sub(Const(1)))
    }
//    val nestedDec = {
//      Dec('a, ArrExpr(ArrExpr(LoInt(), Const(10)), Const(20)))
//    }
    val arrOp = {
      Dec('a, Ptr(Arr(LoInt()))) + HeapAlloc('a, Some(10)) +
      Reverse(Deref('a), Some(ArrOpRange(0, NumEntries(Deref('a))/2)))
    }
    def test(code: LoAst) = {
      Given("Code:\n"+code.tabStr(Indent))
      val top = TypedLoAst(code)
      val xf = ArrayStructs(top)
      Then("Arrays should change to structs in \n"+xf.ast.tabStr(Indent))
      val ctx = new LoInterp()
      val res = ctx.eval(xf)
      (ctx, xf.scope)
    }
    it("Should handle a simple array declaration.") {
      test(simpleDec)
    }
    it("Should allow assignment to elements of simple arrays.") {
      test(simpleDec+simpleAssign)
    }
//    it("Should handle nested array declarations.") {
//      test(nestedDec)
//    }
//    it("Should allow assignment to elements of nested arrays.") {
//      val (env, scope) = test(nestedDec+nestAssign)
//      checkEquiv(env, scope, Deref('x), 888)
//      checkEquiv(env, scope, 'z, 888)
//    }
    it("Should handle array ops.") {
      test(arrOp)
    }
  }

  describe("Record Group Elimination") {
    val UG1 = SplitRecord(Record.Group(LoInt()), Record.Group(LoInt()))
    def test(code: LoAst) = {
      import ressort.lo.interp._
      Given("Code:\n"+code.tabStr(Indent))
      val top = TypedLoAst(code)
      val xf = RecGroupEliminator(top)
      Then(""+xf.ast.tabStr(Indent))
      val ctx = new LoInterp()
      val res = (ctx.eval(xf))
      (ctx, xf.scope)
    }
    it ("Should turn arrays of record groups into structs of record arrays") {
      val code = {
        Block(List(
          Dec('x, Ptr(Arr(UG1))),
          HeapAlloc('x, Some(10)),
          Dec('y, UG1),
          ForBlock('i, NumEntries(Deref('x)),
            (UField(Deref('x).sub('i), 0) := Const(0)) +
            (UField(Deref('x).sub('i), 1) := Const(0)) +
            ('y := Deref('x).sub('i))),
          (UField(Deref('x).sub(1), 0) := Const(0xCAFE))))
      }
      Given(s"Code with a UGroup of tyep $UG1:\n${code.tabStr(3)}")
      val top = TypedLoAst(code)
      val newOp = RecGroupEliminator(top)
      Then(s"That should produce a new code block:\n${newOp.ast.tabStr(3)}")
      val aop = ArrayStructs(newOp)
      And(s"The ArrayStructs transform should also work:\n${aop.ast.tabStr(3)}")
      val (env, scope) = test(newOp.ast)
      checkEquiv(env, scope, UField(Deref(Deref('x).dot('group_0)).sub(1), 0), 0xCAFE)
      checkEquiv(env, scope, UField(Deref(Deref('x).dot('group_1)).sub(1), 0), 0)
    }
  }
}
