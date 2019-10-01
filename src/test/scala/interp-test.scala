package ressort.lo.interp
import ressort.lo._
import ressort.lo.interp._
import org.scalatest._
import org.scalatest.matchers.ShouldMatchers

class InterpSpec extends FunSpec with GivenWhenThen {
  def indent(o: LoAst) = "\n"+o.tabStr(4)+"\n"

  def eval(ast: TypedLoAst): (LoInterp, Option[EVal]) = {
    val ctx = new LoInterp()
    val ret = ctx.eval(ast)
    (ctx, ret)
  }

  def checkEquiv(
      env: LoInterp,
      scope: Symtab,
      lv: LValue,
      n: Long, 
      loType: IntValued=LoInt()): Unit = {
    val res = env.valueOf(lv, scope).toEInt(None)
    val corr = EInt(n, loType)
    assert(res.equiv(corr, None), s"$lv ($loType : $res ${res.i}) != $corr\n ${env}")
    Then(s"$lv should be equal to EInt($n, $loType)")
  }

  describe("A Value Environment") {
    it("Should evaluate integer expressions") {
      val env = Symtab(Map(
        'x -> LoInt(),
        'y -> LoInt()))
      val vars = LoInterp(
        Map(
          SymbolToId('x) -> EInt(10),
          SymbolToId('y) -> EInt(5)), 
        env)
      val expr = 'x * ('y+1)
      Given("An expression "+expr)
      val texpr = env(expr)
      assert(texpr.loType === LoInt())
      assert(vars.eval(texpr) === EInt(10 * (1+5)))
      Then("That should evaluate to 60")
    }
    it("Should deal with unsigned arithmetic") {
      val code = {
        DecAssign('x, UInt32(), 0) +
        ('x := 'x - 1) +
        Dec('y, LoInt()) +
        If('x > 9,
          ('y := 10)) +
        If('x < 9,
          ('y := 7))
      }
      Given("Code:\n"+indent(code))
      val tc = TypedLoAst(code)
      val (env, ret) = eval(tc)
      checkEquiv(env, tc.scope, 'x, (1L << 32)-1, UInt32())
      Then("x should be -1")
      checkEquiv(env, tc.scope, 'y, 10)
      And("y should be 10")

      val signedCode = {
        DecAssign('x, LoInt(), 0) +
        ('x := 'x - 1) +
        Dec('y, LoInt()) +
        If('x > 9,
          ('y := 10)) +
        If('x < 9,
          ('y := 7))
      }
      Given("a *SIGNED* version of the same code: "+indent(code))
      val tc2 = TypedLoAst(signedCode)
      val (env2, ret2) = eval(tc2)
      checkEquiv(env2, tc2.scope, 'y, 7)
      Then("y should now be 7 instead.")

    }
    it("Should handle floating point expresions") {
      val code = {
        ('x := (LoFloat(), FloatConst(1.4142135f))) +
            ('y := (LoFloat(), FloatConst(1.4142136f))) +
            ('z := (LoFloat(), 'x * 'y))
      }
      Given(s"Code with floats:\n"+indent(code))
      val tc = TypedLoAst(code)
      val (env, ret) = eval(tc)
      val zfin = env.valueOf('z, tc.scope).toEFloat(None)
      Then(s"That should run and produce 'z: $zfin")
      And("'z should be 2.0")
    }
    it("Should generate a EContext from a block of declarations and updates") {
      val code = {
        Dec('x, LoInt()) + 
        Dec('y, LoInt()) + 
        Dec('z, LoInt()) +
        Dec('n, LoInt()) +
        Assign('x, 10) + 
        Assign('y, 5) +
        Assign('z, 'x * ('y + 1)) +
        Assign('n,'x)
      }
      val tc = TypedLoAst(code)
      Given("An op sequence "+indent(code))
      val (env, ret) = eval(tc)
      When("that type-checks")
      checkEquiv(env, tc.scope, 'z, 60)
      checkEquiv(env, tc.scope, 'n, 10)
    }
    it("Should evaluate simple for loops") {
      val code = Dec('x, LoInt()) +
        Dec('y, LoInt()) +
        Assign('y, 0) + 
        ForBlock('x, 10, 
          Assign('y, 'y+'x))
      val tc = TypedLoAst(code)
      Given("An op sequence "+indent(code))
      val (env, ret) = eval(tc)
      checkEquiv(env, tc.scope, 'y, 45)
    }
    it("Should evaluate while loops") {
      val code = {
        DecAssign('x, LoInt(), 5) +
        While('x > 2,
          Assign('x, 'x-1))
      }
      val tc = TypedLoAst(code)
      Given("An Op sequence "+indent(code))
      val (env, ret) = eval(tc)
      checkEquiv(env, tc.scope, 'x, 2)
    }
    it("Should evaluate nested loops with complex bodies") {
      val code = 
        Dec('y, LoInt()) +
        Assign('y, 0) +
        ForBlock('x, 10, 
          Assign('y, 'y +'x) +
          ForBlock('z, 10, 
            Assign('y, 'y + 1)))
      Given("An op sequence:\n"+indent(code))
      val tc = TypedLoAst(code)
      Then("That should type-check.")
      val (env, ret) = eval(tc)
      checkEquiv(env, tc.scope, 'y, 145)

      val code2 = {
        Dec('x, UInt()) +
        Dec('y, UInt()) +
        Dec('z, UInt()) +
        Assign('x, 11) +
        Assign('z, 10) +
        ForBlock('x, 'x,
          ForBlock('z, 'z,
            Assign('y,'z)))
      }
      val tc2 = TypedLoAst(code2)
      Given("code:\n"+indent(code2))
      val (env2, ret2) = eval(tc2)
      checkEquiv(env2, tc2.scope, 'y, 9, UInt())
    }
    it("Should evaluate loop strides") {
      val stridedFor = {
        DecAssign('sum, LoInt(), 0) +
        ForSeq('i, 0, 20, 4,
          ('sum := 'sum + 1))
      }
      Given("a strided for loop\n"+stridedFor.tabStr(3))
      val tc = TypedLoAst(stridedFor)
      val (env, ret) = eval(tc)
      Then("that code should type-check and evalute")
      checkEquiv(env, tc.scope, 'sum, 5)
      And("it should execute exactly 20/4=5 times")
    }
    it("Should evaluate boolean expressions") {
      val p = Id("p")
      val q = Id("q")
      val code = Dec('p, Bool()) +
        Dec('q, Bool()) +
        Dec('x, LoInt()) +
        Assign('p, False) +
        Assign('x, 5) + 
        Assign('q, ('x > 1) && Not('p))
      Given("An op seq:\n" + indent(code))
      val tc = TypedLoAst(code)
      Then("That should type-check")
      val (env, ret) = eval(tc)
      assert(env.valueOf('q, tc.scope) === EBool(true))
      assert(env.valueOf('p, tc.scope) === EBool(false))
      And("q should be true and p should be false and so should you")
    }
    it("Should evaluate Mux expressions") {
      def maxTest(xval: Int, yval: Int) {
        val code = {
          DecAssign('x, LoInt(), Const(xval)) +
          DecAssign('y, LoInt(), Const(yval)) +
          DecAssign('z, LoInt(), Mux('x > 'y, 'x,'y))
        }
        Given("Code:\n"+code.tabStr(3))
        val tc = TypedLoAst(code)
        Then("That should type-check")
        val (env, ret) = eval(tc)
        if(xval > yval) {
          checkEquiv(env, tc.scope, 'z, xval)
        } else {
          checkEquiv(env, tc.scope, 'z, yval)
        }
      }
      maxTest(10, 15)
      maxTest(270, 15)
    }
    it("Should correctly handle if statements") {
      val code = Dec('x, LoInt()) +
        Dec('y, LoInt()) + 
        Assign('x, 5) +
        Assign('y, 7) +
        If('x > 'y, 
          Assign('y, 0)) +
        If('x < 'y,
          Assign('x, 0))
      Given("An op seq:\n" + indent(code))
      val tc = TypedLoAst(code)
      Then("That should type-check")
      val (env, ret) = eval(tc)
      checkEquiv(env, tc.scope, 'x, 0)
      checkEquiv(env, tc.scope, 'y, 7)
    }
    it("Should correctly handle if-else statements") {
      val code = Dec('x, LoInt()) +
        Dec('y, LoInt()) + 
        Assign('x, 5) +
        Assign('y, 7) +
        IfElse('x > 'y, 
          Assign('y, 0),
          Assign('x, 0))
      Given("An op seq:\n" + indent(code))
      val tc = TypedLoAst(code)
      Then("That should type-check")
      val (env, ret) = eval(tc)
      checkEquiv(env, tc.scope, 'x, 0)
      checkEquiv(env, tc.scope, 'y, 7)
    }
  }
  describe("Pointers and arrays") {
    it("Should allow pointer reference/dereference") {
      val ptr = Id("ptr")
      val code = {
        Dec('x, LoInt()) +
        Dec('y, LoInt()) +
        Dec('ptr, Ptr(LoInt())) +
        Assign('x, 17) +
        Assign('y, 3) +
        Assign('ptr, Ref('y)) +
        Assign('x, 'x + Deref('ptr))
      }
      Given("op seq:\n" + indent(code))
      val tc = TypedLoAst(code)
      Then("That should type-check")
      val (env, ret) = eval(tc)
      checkEquiv(env, tc.scope, 'x, 20)
      checkEquiv(env, tc.scope, 'y, 3)

      val code2 = code + {
        Assign(Deref('ptr), 'x + 1)
      }
      Given("expanded seq:\n"+indent(code2))
      val tc2 = TypedLoAst(code2)
      val (env2, ret2) = eval(tc2)
      checkEquiv(env2, tc2.scope, 'y, 21)
      Then("y should be 21")
      checkEquiv(env2, tc2.scope, 'x, 20)
    }

    it("Should handle simple arrays and arrays of references") {
      val arr = Deref('arr)
      val code = {
        Dec('x, LoInt()) +
        Dec('arr, Ptr(Arr(LoInt()))) +
        HeapAlloc('arr, Some(10)) +
        Assign(arr.sub(0), 17) +
        Assign(arr.sub(1), 101) +
        Assign('x, arr.sub(0))
      }
      val tc = TypedLoAst(code)
      Given("code:\n" + indent(code))
      val (env, ret) = eval(tc)
      Then("That should execute")
      checkEquiv(env, tc.scope, 'x, 17)
      checkEquiv(env, tc.scope, arr.sub(1), 101)

      val code2 = {
        Dec('arr, Ptr(Arr(Ptr(LoInt())))) +
        HeapAlloc('arr, Some(3)) +
        Dec('x, LoInt()) +
        Dec('y, LoInt()) +
        Assign(arr.sub(0), Ref('x)) +
        Assign(arr.sub(1), Ref('y)) +
        Assign('x, 1024) +
        Assign('y, 2048)
      }
      val tc2 = TypedLoAst(code2)
      Given("code:\n"+indent(code))
      val (env2, ret2) = eval(tc2)
      Then("that should also execute")
      checkEquiv(env2, tc2.scope, Deref(arr.sub(0)), 1024)
      checkEquiv(env2, tc2.scope, Deref(arr.sub(1)), 2048)
    }


    it("Should support HeapAlloc()s") {
      val code = {
        Dec('x, Ptr(Arr(LoInt()))) +
        HeapAlloc('x, Some(10)) +
        Assign(Deref('x).sub(0), 17) +
        Assign(Deref('x).sub(1), 25) +
        DecAssign('y, LoInt(), NumEntries(Deref('x)))
      }
      Given("Code:\n"+indent(code))
      val tc = TypedLoAst(code)
      Then("That should type check")
      val (env, ret) = eval(tc)
      And("It should execute")
      checkEquiv(env, tc.scope, Deref('x).sub(0), 17)
      checkEquiv(env, tc.scope, Deref('x).sub(1), 25)
      checkEquiv(env, tc.scope, 'y, 10)
    }
     
    it("Should support Free()s") {
      val goodCode = {
        Dec('x, Ptr(Arr(LoInt()))) +
        HeapAlloc('x, Some(10)) +
        Assign(Deref('x).sub(0), 17) +
        Assign(Deref('x).sub(1), 25) +
        DecAssign('y, LoInt(), NumEntries(Deref('x))) +
        Free('x)
      }
      Given("Code:\n"+indent(goodCode))
      val tc = TypedLoAst(goodCode)
      Then("That should type check")
      val (env, ret) = eval(tc)

      val useAfterFree = {
        goodCode + 
        DecAssign('z, LoInt(), Deref('x).sub(0))
      }
      Given("Bad code (use after free):\n"+indent(useAfterFree))
      val tc2 = TypedLoAst(useAfterFree)
      Then("That should also type check")
      val err = intercept[AssertionError] {
        val (env2, ret2) = eval(tc2)
      }
      And("It should yield an error message when executed:\n"+
        ressort.util.indent(err.getMessage(),2))
    }
  }

  describe("Functions") {
    it("Should handle simple functions") {
      val code = {
        FuncDec('f, List('x -> LoInt(), 'y -> Ptr(LoInt())), {
            Deref('y) := 'x * 'x 
          } ) +
        DecAssign('y, LoInt(), 0) +
        App('f, List( 'x-> 10, 'y -> Ref('y)))
      }
      Given("Code:\n"+indent(code))
      val tc = TypedLoAst(code)
      Then("it should type-check")
      val (env, ret) = eval(tc)
      And("it should execute")
      assert(env.valueOf('y, tc.scope).toEInt(None).equiv(EInt(100, LoInt()), None),
        "Env: "+env+"\nscope:\n"+tc.scope.altToString+"\n")
      And("y should be 100")
    }
    it("Should allow multiple functions that call each other") {
      val size = 4
      val code = {
        FuncDec('sum, List('n->UInt(), 'y->Ptr(Arr(LoInt()))),
          {
            val yy = Deref('y)
            (yy.sub('n+1) := yy.sub('n+1) + yy.sub('n))
          })+
        FuncDec('init, List('x->UInt(), 'y->Ptr(Arr(LoInt()))),
          ForBlock('n, 'x, 
            Deref('y).sub('n) :='n)) +
        DecAssign('x, LoInt(), Const(size))+
        Dec('y, Ptr(Arr(LoInt()))) +
        HeapAlloc('y, Some('x)) +
        FuncDec('f, List( 'x->UInt(), 'y->Ptr(Arr(LoInt()))), {
            ForBlock('n, 'x-1, {
                App('sum, List('n->'n, 'y->'y))
              })
          }) +
        App('init, List('x->Const(size), 'y->'y)) +
        App('f, List('x->Const(size), 'y->'y))
      }
      Given("Code:\n"+indent(code))
      val tc = TypedLoAst(code)
      Then("It should type-check.")
      val (env, ret) = eval(tc)
      And("It should execute.")
      val correct = {
        def pfxSum(l: List[Int], sum: Int=0): List[Int] = l match {
          case h::Nil => (h+sum)::Nil
          case h::t => (h+sum)::pfxSum(t, h+sum)
          case Nil => Nil
        }
        pfxSum((0 until size).toList)
      }
      val measured = (0 until size) map { 
        n => env.valueOf(Deref('y).sub(Const(n)), tc.scope).toEInt(None).i
      }
      assert(measured === correct, "Env: "+env)
      And("should give a correct prefix sum")     
    }
    it("Should correctly remove functions when they go out of scope") {
      val code = {
        FuncDec('F, List('n->Ptr(LoInt())), {
            FuncDec('sq, List('i->Ptr(LoInt())), {
                val ii = Deref('i)
                ( ii := ii * ii)
              }) +
            App('sq, List('i->'n))
          }) +
        DecAssign('x, LoInt(), 7) +
        App('F, List('n->Ref('x)))
      }
      val tc = TypedLoAst(code)
      Given("Code: \n"+indent(code))
      val (env, ret) = eval(tc)
      checkEquiv(env, tc.scope, 'x, 49)
      intercept[AssertionError] { env.valueOf('sq, tc.scope) }
      Then("There should be no value for sq()")
    }
    it("Should support functions with a return value") {
      val loopEscape = {
        FuncDec('f, List('x -> Ptr(LoInt())), {
          ForBlock('y, 10,
            IfElse('y < 5,
              Assign(Deref('x),'y),
              Block(Nop::Nop::Return('y)::Nop::Nil))) +
            Return(Const(-1))
          }, 
          Some(LoInt())) +
        Dec('z, LoInt()) +
        Dec('n, LoInt()) +
        Assign('n, 10) +
        AssignReturn('n, App('f, List('x -> Ref('z))))
      }
      Given("A function with a return in the middle of a loop\n"+loopEscape)
      val leTop = TypedLoAst(loopEscape)
      val (leTopEnv, _) = eval(leTop)
      val zval = leTopEnv.valueOf('z, leTop.scope)
      assert(zval.toEInt(None).equiv(EInt(4, LoInt()), None))
      Then("Execution should stop when return is reached: z="+zval)
      checkEquiv(leTopEnv, leTop.scope, 'n, 5, UInt())
    }
  }
  describe("Struct support") {
    val Point = Id("Point")
    val pdec = {
      Typedef(Struct(Point, List('x -> LoInt(), 'y -> LoInt()))) +
      Dec('p, TypeRef(Point)) +
      (Field('p,'x) := 2) +
      (Field('p,'y) := 3)
    }
    
    val lsDec = {
      val point = Struct(Point, List('x -> LoInt(), 'y -> LoInt()))
      Typedef(point) +
      Typedef(Struct('LineSeg, List('p1 -> point, 'p2 -> point))) +
      Dec('l, 'LineSeg) +
      (Field(Field('l, 'p1),'x) := 1) + 
      (Field(Field('l, 'p1),'y) := 2) + 
      (Field(Field('l, 'p2),'x) := 3) + 
      (Field(Field('l, 'p2),'y) := 4)
    }
    it("Should allow the setting of fields") {
      val code = pdec
      Given("Code :\n"+indent(code))
      val tc = TypedLoAst(code)
      val (env, ret) = eval(tc)
      Then("That code should evaluate")
      checkEquiv(env, tc.scope, Field('p, 'x), 2)
      checkEquiv(env, tc.scope, Field('p, 'y), 3)
    }
    it("Should allow nested structures") {
      val code = {
        lsDec +
        DecAssign(
          'dx, 
          LoInt(), 
          Field(Field('l, 'p2),'x) - Field(Field('l, 'p1),'x))
      }
      Given("Code: \n"+indent(code))
      val tc = TypedLoAst(code)
      val (env, ret) = eval(tc)
      Then("That code should evaluate")
      checkEquiv(env, tc.scope, 'dx, 2)
    }
    it("Should support pointers to fields") {
      val code = {
        lsDec +
        DecAssign('p1, Ptr(LoInt()), Ref(Field(Field('l, 'p1),'x))) +
        Assign(Deref('p1), 7)
      }
      Given("Code:\n" + code)
      val tc = TypedLoAst(code)
      val (env, ret) = eval(tc)
      Then("It should evaluate")
      checkEquiv(env, tc.scope, Field(Field('l, 'p1),'x), 7)
      And("It should have set l.p1.x to 7")
      checkEquiv(env, tc.scope, Field(Field('l, 'p1), 'y), 2)
      checkEquiv(env, tc.scope, Field(Field('l, 'p2),'x), 3)
      checkEquiv(env, tc.scope, Field(Field('l, 'p2),'y), 4)
      And("All other values should have stayed the same")
    }
    it("Should throw a proper exception on access to uninitialized var") {
      val code = {
        Dec('x, LoInt()) +
        DecAssign('y, LoInt(), 'x+1)
      }
      val tc = TypedLoAst(code)
      Given("Code:\n"+indent(code))
      val err = intercept[AssertionError] {
        val (env, ret) = eval(tc)
      }
      Then("It should give an error message:\n\t"+err)
    }
    it("Should allow a Typedef to be accessed from within a function") {
      val code = {
        Typedef(Struct(Point, List('x -> LoInt(), 'y -> LoInt()))) +
        FuncDec('z, List('x -> Ptr(LoInt())),
          Dec('p, TypeRef(Point)) +
          ('p.dot('x) := Deref('x)) +
          ('p.dot('y) := 5) +
          (Deref('x) := 'p.dot('x) + 'p.dot('y))) +
        DecAssign('x, LoInt(), 7) +
        App('z, List('x -> Ref('x)))
      }
      Given("Code:\n"+code)
      val tc = TypedLoAst(code)
      val (env, ret) = eval(tc)
      Then("It should evaluate.")
      checkEquiv(env, tc.scope, 'x, 12)
    }

  }

  describe("Array ops") {
    val makeArr = {
      Dec('arr, Ptr(Arr(LoInt()))) +
      HeapAlloc('arr, Some(10)) +
      IPar('i, 10, Deref('arr).sub('i) := 'i)
    }
    val intArr = (0 until 10)
    
    def fromEArr(
        earr: EArray,
        env: LoInterp): Array[Int] = {
      val list = earr.a map { _.value.toEInt(None).i.toInt }
      list.toArray
    }

    def test(code: LoAst, correct: Array[Int]) {
      Given("code: \n"+code.tabStr(3))
      val tc = TypedLoAst(code)
      Then("that should type-check")
      val (env, ret) = eval(tc)
      And("it should evaluate.")
      val earr = env.valueOf(Deref('arr), tc.scope).toEArray(None)
      val res = fromEArr(earr, env)
      val errStr = {
        "The result should be\n"+
        "\t\t"+correct.toList+"\n"+
        "\t\t(actual result: "+res.toList+")"+"\n"
      }
      assert(res.toList == correct.toList, errStr)
      And(errStr)
    }

    it("should reverse a subarray") {
      val code = {
        makeArr +
        Reverse(Deref('arr), Some(ArrOpRange(0, 5)))
      }
      val correct = Array(4, 3, 2, 1, 0, 5, 6, 7, 8, 9)
      test(code, correct)
    }

    it("should rotate a subarray in both directions") {
      val code = {
        makeArr + 
        RotRight(Deref('arr), 2, Some(ArrOpRange(5, 10))) +
        RotLeft(Deref('arr), 2, Some(ArrOpRange(0, 5)))
      }
      val correct = Array(2, 3, 4, 0, 1, 8, 9, 5, 6, 7)
      test(code, correct)
    }

    it("should do prefix sums") {
      val code = {
        makeArr + 
        PrefixSum(Deref('arr), Some(ArrOpRange(1,6)))
      }
      val correct = Array(0, 0, 1, 3, 6, 10, 6, 7, 8, 9)
      test(code, correct)
    }

    it("should do memsets") {
      val code = {
        makeArr +
        Memset(Deref('arr), 999, Some(ArrOpRange(3, 7)))
      }
      val correct = Array(0, 1, 2, 999, 999, 999, 999, 7, 8, 9)
      test(code, correct)
    }
  }
}
