package ressort.lo
import ressort.util._
import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen
import org.scalatest.matchers.ShouldMatchers
import scala.collection.mutable.Stack

class ExprSpec extends FunSpec with GivenWhenThen {
  describe("The Expr base class") {
    it("Should print infix expressions reasonably well") {
      Given("1+x*(3/4)+5")
      val exp = 1+Id("x")*(3/4)+5
      Then("it prints: " + exp)
    }
    it("Should generate a Less(..) Expr from the < operator") {
      Given("Const(5) < Const(6)")
      val e = Const(5) < 'a
      Then("It should produce a Less()-typed Expr: made "+e)
      e match {
        case Less(_, _) => 
        case _ => fail(e.toString)
      }
    }
  }
}

class TypeSpec extends FunSpec with GivenWhenThen {
  describe("An LoType subclass") {
    it("should accept() an equivalent type") {
      val lvInt = LoInt()
      Given(s"an LValue type $lvInt")
      assert(lvInt.accepts(LoInt(false)))
      Then("that should accept() an LoInt")
      assert(lvInt.accepts(LoInt(true)))
      And("that should accept() an LoInt(const=true)")
      assert(lvInt.accepts(UInt(true)))
      And("it should also accept() a UInt(true)")
    }
  }
}

class SymtabSpec extends FunSpec with GivenWhenThen {

  describe("A Symtab") {
    it("Should associate NoType with a variable") {
      When("It is empty")
      val te = new Symtab()
      val anyId = Id("x")
      val otherId = Id("y")

      Then("symType should return None always")
      assert(te.symType(anyId) === None)
      assert(te.symType(otherId) === None)
      And("all results of that call should be equal")
      assert(te.symType(anyId) === te.symType(otherId))
    }

    it ("Should update implement a parent-child relationship") {
      Given("An empty environment")
      val emptyTE = new Symtab()
      val v = Id("v")
      val vtype = Arr(LoInt())
      val child = {
        val tab = (new Symtab(Some(emptyTE)))
        tab.add(v, vtype)
        tab
      }
      assert(child.symType(v).get ===  vtype)
      Then("Calling update should create a child that assigns type to a var")

      assert(emptyTE.symType(v) === None)
      And("the parent should still return NoType")

      assert(child.parent === Some(emptyTE))
      And("The child's .parent should be equal to the parent environment.")

      assert(emptyTE.dominates(child))
      And("The parent should dominate the child")

      assert(!child.dominates(emptyTE))
      And("The child should not dominate the parent")
    }
  }
}

class OpCheckerSpec extends FunSpec with GivenWhenThen {
  describe("Basic Ops") {
    it("should build a correct TypedLoOp tree from an Seq with Decs") {
      Given("a declaration of a var of LoInt() type")
      val dec = Dec('x, LoInt())
      val typedDec = TypedLoAst(dec)
      Then("the generated tree should have a leaf with a new env")
      assert(typedDec.scope.symType('x).get === LoInt())
      assert(typedDec.children === Nil)

      Given("an op: Dec(x, Int); Dec(y, Int); x=5, y=3;  If(x > y) { x <-- 1 }")
      val dec2 = Dec('y, LoInt())
      val env = (TypedLoAst(dec+dec2)).scope
      Then("It should make a scope "+env.altToString)
      val xTypeNew = env.symType('x).get
      val yTypeNew = env.symType('y).get
      assert(xTypeNew === LoInt(), "New x type is "+xTypeNew)
      assert(yTypeNew === LoInt(), "New y type is "+yTypeNew)
      Then("after declarations, x and y should have LoInt() types")
      val updates = Assign('x, 5) + Assign('y, 3)
      val iff = If('x > 'y, Assign('x, 1))
      val typedOp = TypedLoAst(dec+dec2+updates+iff)
    }
    it("Should handle an empty Block()") {
      val code = Block(Nil)
      Given("code: "+code)
      val top = TypedLoAst(code)
      Then("that should type-check.")
    }
    it("Should handle HeapAlloc statements") {
      val code1 = {
        Dec('x, Ptr(Arr(LoInt()))) +
        HeapAlloc('x, Some(100))
      }
      Given("Input op " + code1)
      val top = TypedLoAst(code1)
      Then("That should type-check")
      val code2 = {
        Dec('x, Arr(LoInt())) +
        HeapAlloc('x, Some(10))
      }
      Given("Another input op " + code2)
      val thrown = intercept[AssertionError] { TypedLoAst(code2) }
      val err = indent(thrown.toString, 3)
      Then("That should fail type checking with error \n"+err)
    }

    it("Should build a new env for loops' implicit index declarations") {
      val len = 32
      val block = {
        Dec('y, Ptr(Arr(LoInt()))) +
        HeapAlloc('y, Some(len * len)) +
        IPar('i, len,
          IPar('j, len,
            Assign(Subsc(Deref('y), 'i*len+'j), 'i*len+'j)))
        }
        Given("A block :\n" + indent(block))
        val ttree = TypedLoAst(block)
        val assign = ttree.children(2).children(0).children(0)
        assert(assign.scope.symType('j).get.nonConst === Index())
        Then("The innermost node's env should assign Index type to index i")
    }

    it("should type-check while loops") {
      val code = {
        ('x := (LoInt(), 0)) +
        While('x < 10,
          ('x := 'x + 1))
      }
      Given("code:\n"+indent(code))
      val top = TypedLoAst(code)
      Then("that should type-check")

      val badCode = {
        ('x := (LoInt(), 0)) +
        While('x + 1,
          ('x := 'x + 1))
      }
      Given("a while loop with non-boolean condition:\n"+indent(code))
      val thrown = intercept[AssertionError] { TypedLoAst(badCode) }
      val err = indent(thrown.toString, 3)
      Then("that chould fail type checking with error\n"+err)
    }

    it("Should allow only integer types in strides") {
      val badCode = {
        ('sum := (UInt(), 0)) +
        ForSeq('i, 0, 20, True, ('sum := 'sum + 'i))
      }
      Given("a loop with bool-valued 'stride':\n"+indent(badCode))
      val thrown = intercept[AssertionError] { TypedLoAst(badCode) }
      Then("that should throw and exception:\n"+indent(thrown.toString, 3))

      val goodCode = {
        ('sum := (UInt(), 0)) +
        ForSeq('i, 0, 20, 5, ('sum := 'sum + 'i))
      }
      Given("a good loop with a stride of 5:\n"+goodCode.tabStr(3))
      val top = TypedLoAst(goodCode)
      Then("that should type-check")
    }
  }

  describe("Constant types") {
    it("should allow declaration of constants with DecAssign") {
      val cdec = {
        DecAssign('x, LoInt(const=true), -1) +
        DecAssign('y, LoInt(), -2) +
        ('y := 'x)
      }
      Given("code:\n"+indent(cdec))
      val top = TypedLoAst(cdec)
      Then("that should type-check")
    }

    it("should given an error when assigning to a const") {
      val badAssign = {
        DecAssign('x, LoInt(const=true), 0) +
        ('x := 1)
      }
      Given("code with attempted assign to const:\n"+indent(badAssign))
      val thrown = intercept[AssertionError] { TypedLoAst(badAssign) }
      Then("that should fail with error:\n"+indent(thrown.toString, 3))
    }

    it("should allow const pointers to mutable values") {
      val cdec = {
        DecAssign('x, LoInt(), 0) +
        DecAssign('ptr, Ptr(LoInt(true)), Ref('x)) +
        DecAssign('y, LoInt(), Deref('ptr))
      }
      Given("code:\n"+indent(cdec))
      val top = TypedLoAst(cdec)
      Then("that should type-check")

      val bad = {
        cdec +
        (Deref('ptr) := 1)
      }
      Given("non const-correct code:\n"+indent(bad))
      val thrown = intercept[AssertionError] { TypedLoAst(bad) }
      Then("that should fail with error:\n"+indent(thrown.toString, 3))
    }

    it("should not allow mutations sub-LValues of const-typed objects") {
      val cdec = {
        Dec('arr, Ptr(Arr(LoInt(false)))) +
        HeapAlloc('arr, Some(10)) +
        DecAssign('ptr, Ptr(Arr(LoInt(false), true), false), ('arr))
      }
      Given("valid pointer declaration code:\n"+indent(cdec))
      val top = TypedLoAst(cdec)
      Then("that should type-check")
     
      val goodAssign = {
        (Deref('arr).sub(0) := 10)
      }
      Given("a legal assignment through the array:\n"+indent(goodAssign))
      val top2 = TypedLoAst(cdec + goodAssign)
      Then("that should also type-check")

      val badAssign = {
        (Deref('ptr).sub(0) := 10)
      }
      Given("bad assignment to a const array element:\n"+indent(badAssign))
      val thrown = intercept[AssertionError] { TypedLoAst(cdec + badAssign) }
      Then("that should fail with an error:\n"+indent(thrown.toString, 3))
    }
  }


  describe("Functions") {
    val fdec =  {
      Dec('z, LoInt()) +
      Dec('t, Record(UInt32())) +
      FuncDec('f, List('x -> LoInt(), 'y -> Ptr(LoInt())),
        Assign(Deref('y), 'x * 'x))
    }
    it("Declaration should create a new env from (new Symtab()) for the body") {
      Given("A function declaration:\n"+indent(fdec))
      val ttree = TypedLoAst(fdec)
      val bodyOp = ttree.children(2).children(0)
      val env = bodyOp.scope
      assert(env.symType('x).get === LoInt())
      assert(env.symType('y).get === Ptr(LoInt()))
      Then("x should have type Int and y should have type Ptr(Int) in body.")
    }
    it("Application should type check actual params against formal") {
      val fapp = fdec + 'f('x->2, 'y->Ref('z))
      val ttree = TypedLoAst(fapp)
      Then(
        "An application\n"+indent(fapp)+
        " should type check")
      val fappFail = fdec + 'f('x->'t, 'y->Ref('z))
      val thrown = intercept[AssertionError] { TypedLoAst(fappFail) }
      Then(
        "The appl\n"+indent(fappFail)+
        " should Fail with msg\n"+indent(thrown.toString, 3))
    }
    
    it("Should match actual parameter names against formal") {
      val badApp = fdec + 'f('x -> 2, 'z->Ref('z))
      Given("An appliction with an incorrect argument name: "+badApp.tabStr(3))
      val thrown = intercept[AssertionError] { TypedLoAst(badApp) }
      Then("That should fail with error:\n"+indent(thrown.toString, 3))
    }
    
    it("Should not allow more/fewer actual than formal parameters") {
      val badApp1 = fdec + 'f('x->2, 'y->Ref('z), 't -> Const(1))
      Given(
        "A function application with too many arguments:"+
        indent(badApp1))
      val thrown = intercept[AssertionError] { TypedLoAst(badApp1) }
      Then("That should fail with message "+indent(thrown.toString, 3))
      
      val badApp2 = fdec + 'f('x->2)
      Given(
        "A function applicaiton with fewer actual than formal parameters:"+
        indent(badApp2))
      val thrown2 = intercept[AssertionError] { TypedLoAst(badApp2) }
      Then("That should fail with message "+indent(thrown2.toString, 3))
    }

    it("Should support functions with return values") {
      val retFunc = {
        FuncDec('f, List('x -> LoInt()), {
            DecAssign('y, LoInt(), 'x*'x) +
            Return('y)
          }, Some(LoInt()))
      }
      Given("An LoInt()-valued func "+retFunc)
      val top = TypedLoAst(retFunc)
      Then("That should type-check")

      val badFunc = {
        FuncDec('f, List('x -> LoInt()), {
            DecAssign('y, LoInt(), 'x*'x) +
            Return(Ref('x))
          }, Some(LoInt()))
      }
      Given("A function that returns a value of the wrong type "+badFunc)
      val thrown = intercept[AssertionError] { TypedLoAst(badFunc) }
      Then("That should fail type checking with error "+thrown)

      val badFunc2 = {
        FuncDec('f, List('x -> LoInt()), {
            DecAssign('y, LoInt(), 'x*'x) +
            IfElse('y > 100,
              Assign('x, 'x+'x),
              Return('x))
          },
          Some(LoInt()))
      }
      Given("An IfElse whose clauses return diff types"+badFunc2)
      val thrown2 = intercept[AssertionError] { TypedLoAst(badFunc2) }
      Then("That should fail to type check with error "+thrown2)

      val goodFuncIf = {
        FuncDec('f, List('x -> LoInt()),
          IfElse('x > 10,
            Return('x * 2),
            Return('x * 'x)),
          Some(LoInt()))
      }
      Given("An IfElse whose clauses both return the same type:\n"+goodFuncIf)
      val topGoodFuncIf = TypedLoAst(goodFuncIf)
      Then("That should type-check")

      val uintToInt = {
        FuncDec('f, List('x -> UInt()),
          Return('x + 1),
          Some(LoInt())) +
        Dec('y, LoInt()) +
        AssignReturn('y, 'f('x -> Const(10)))
      }
      Given(
        "A function that returns an LoInt() and Return()s a UInt:\n"+
        uintToInt.tabStr(3))
      val topUIntToInt = TypedLoAst(uintToInt)
      Then("That should type-check")

      val uintToIntArg = {
        FuncDec('f, List('x -> LoInt()),
          Return('x + 1),
          Some(LoInt())) +
        DecAssign('z, LoInt(), 0) +
        ForBlock('y, 100,
          AssignReturn('z, 'f('x->'y)))
      }
      Given(
        "Code that passes a UInt to an LoInt() arg:\n"+
        uintToIntArg.tabStr(3))
      val topUIntToIntArg = TypedLoAst(uintToIntArg)
      Then("That should type-check")
    }


    def makePassingIntTest(fromType: IntValued, toType: IntValued) = {
      val code = {
        Dec('x, fromType) +
        Dec('y, toType) +
        ('y := 'x)
      }
      Given(
        s"Code that makes a legal implicit cast from $fromType to $toType:\n"+
        code.tabStr(3))
      val top = TypedLoAst(code)
      Then("That code should type-check.")
    }
    makePassingIntTest(UInt32(),  LoInt32())
    makePassingIntTest(LoInt32(), UInt32())
    makePassingIntTest(UInt8(),   LoInt32())
    makePassingIntTest(UInt32(),  LoInt64())
    makePassingIntTest(UInt16(),  Index())
  }

  describe("Struct type support") {
    it("Should approve simple field accesses") {
      Given("Struct type "+'Point)
      val code = {
        Typedef(Struct('Point, List('x -> LoInt(), 'y -> LoInt()))) +
        Dec('p, 'Point) +
        (Field('p, 'x) := 10)
      }
      And("Code:\n"+indent(code))
      TypedLoAst(code)
      Then("That should type-check")
    }
    it("Should deny the type of non-existent fields") {
      val badCode = {
        Typedef(Struct('Point, List('x -> LoInt(), 'y -> LoInt()))) +
        Dec('p, 'Point) + Assign(Field('p, 'p), 1)
      }
      Given("Bad code "+badCode)
      val thrown = intercept[AssertionError] {
        TypedLoAst(badCode)
      }
      Then("That should fail with error "+thrown)
    }
    it("Should give an error when the reference of a TypeRef is undefined.") {
      val DNE = Id("DoesNotExist")
      val badCode = {
        Dec('x, TypeRef(DNE))
      }
      Given("Code:\n"+badCode.tabStr(3))
      val thrown = intercept[AssertionError] {
        TypedLoAst(badCode)
      }
      Then("That should fail with error "+thrown)
    }
    it("Should allow a Typedef to be accessed from within a function") {
      val code = {
        Typedef(Struct('Point, List('x -> LoInt(), 'y -> LoInt()))) +
        FuncDec('z, List('x -> Ptr(LoInt())),
          Dec('p, TypeRef('Point)) +
          ('p.dot('x) := Deref('x)) +
          ('p.dot('y) := 5) +
          (Deref('x) := 'p.dot('x) + 'p.dot('y))) +
        DecAssign('x, LoInt(), 7) +
        App('z, List('x -> Ref('x)))
      }
      Given("code:\n"+code.tabStr(3))
      val tops = TypedLoAst(code)
      Then("that should type-check.")
    }
  }

  describe("Record groups") {
    val Rg1 = SplitRecord(Record.Group(LoInt()), Record.Group(LoInt()))
    val Rg2 = SplitRecord(Record.Group(LoInt(), LoInt()))
    val Rg3 = SplitRecord(Record.Group(LoInt()))
    val Rg4 = SplitRecord(Record.Group(Bool()), Record.Group(LoInt()))
    val scope = Symtab(Map(
      'x -> Rg1,
      'y -> Rg2,
      'z -> Rg3,
      'a -> Rg4))
    it("should allow assignment between compatible record groups") {
      val stmt = ('x := 'y)
      Given(s"Value ${'x} of type $Rg1 and ${'y} of type $Rg2")
      val top = TypedLoAst(stmt, Some(scope))
      Then(s"$stmt should check")
    }
    it("should disallow assignment between incompatible record groups") {
      val stmt = ('x := 'z)
      Given(s"Value ${'x} of type $Rg1 and ${'z} of type $Rg3")
      val err = intercept[AssertionError] {
        TypedLoAst(stmt, Some(scope))
      }
      Then(s"$stmt should NOT check:\n$err")
      val stmt2 = ('x := 'a)
      Given(s"Value ${'x} of type $Rg1 and ${'a} of type $Rg4")
      val err2 = intercept[AssertionError] {
        TypedLoAst(stmt2, Some(scope))
      }
      Then(s"$stmt2 should also NOT check:\n$err2")
    }
    it("should allow sub-field assignment") {
      val stmt = (UField('x, 0) := UField('y, 1))
      Given(s"Value ${'x} of type $Rg1 and ${'y} of type $Rg2")
      val top = TypedLoAst(stmt, Some(scope))
      Then(s"$stmt should check")
    }

  }

  describe("Array Ops") {
    val decs = {
      Dec('A, Ptr(Arr(UInt()))) +
      HeapAlloc('A, Some(100)) +
      Dec('B, Ptr(Arr(Bool())))+
      HeapAlloc('B, Some(10)) +
      ('C  := (UInt(), 10))
    }
    def makeValidTest(op: LoAst) {
      Given("a valid array op test:\n"+indent((decs+op).toString, 3))
      val top = TypedLoAst(decs+op)
      Then("that should type-check")
    }
    def makeErrTest(op: LoAst) {
      Given("an invalid array op test:\b"+indent((decs+op).toString, 3))
      val err = intercept[AssertionError] { TypedLoAst(decs+op) }
      Then("that should throw an error:\n"+indent(err.toString, 3))
    }

    it("should type-check simple array ops with and without ranges") {
      makeValidTest(RotLeft(Deref('A), 2, None))
      makeValidTest(RotRight(Deref('B), 3, Some(ArrOpRange(3, 5))))
      makeValidTest(Reverse(Deref('B), None))
      makeValidTest(PrefixSum(Deref('A), None))
      makeValidTest(Memset(Deref('A), 0, None))
    }
    it("should give an error for non-int range values") {
      makeErrTest(RotLeft(Deref('A), 2, Some(ArrOpRange(True, False))))
      makeErrTest(Reverse(Deref('B), Some(ArrOpRange(2, True))))
    }
    it("should give an error for non-array type inputs") {
      makeErrTest(RotLeft(Deref('C), 2, None))
    }
    it("should give an error for prefix sum on a non-int array") {
      makeErrTest(PrefixSum(Deref('B), None))
    }
    it("should give an error for an incompatible value type in Memset") {
      makeErrTest(Memset(Deref('B), 0, None))
    }
  }
}

class ExprCheckerTest extends FunSpec with GivenWhenThen {
  describe("Comparison operators") {
    def assertValidBool()(e: Expr)(implicit scope: Symtab) {
      Given("A well-formed comparison "+e)
      val loType = scope.exprChecker(e).right.get.loType
      Then("That should type-check")
      val errMsg = s"Expr $e should be typed Bool(); was typed $loType\n"
      And("The result should be Bool().")
      assert(loType === Bool(), errMsg)
    }
    def assertErrorMismatched(e: Expr)(implicit scope: Symtab) {
      Given("a comparison on unequal types "+e)
      val errs = scope.exprChecker(e).left.get
      val errStr = errs.map("  "+_.err)
      Then("That should fail with errors:\n"+reduceNewline(errStr))
    }
    it("should return a Bool()-type result from well-typed inputs") {
      implicit val scope = (new Symtab())
      assertValidBool()(Less(1, 7))
      assertValidBool()(Equal(True, False))
      assertValidBool()(Less(-1, 10))
    }
    it("should give an error when inputs are of different types") {
      assertErrorMismatched(Equal(1, False))((new Symtab()))
      Given("A value 'r of type Record(UInt())")
      implicit val scope = Symtab(Map('r -> Record(UInt())))
      assertErrorMismatched(Equal('r, 0))
    }
  }

  describe("Logical Operators") {
    def assertValid(e: Expr, t: LoType)(implicit scope: Symtab) {
      Given("valid expression "+e)
      val loType = scope(e).loType
      Then("that should type-check")
      assert(loType.nonConst === t)
      And("its type should be "+t)
    }
    def assertErr(e: Expr)(implicit scope: Symtab) {
      Given("an invalid expression "+e)
      val checkRes = scope.exprChecker(e)
      assert(checkRes.isLeft, s"$checkRes has no error")
      val errs = checkRes.left.get
      val err = reduceNewline(errs.map(_.err))
      Then("that should fail with an error:\n"+indent(err))
    }
    it("should return type Bool() for Bool() inputs") {
      implicit val scope = (new Symtab())
      assertValid(True && False, Bool())
      assertValid(False || True, Bool())
      assertValid(Not(False), Bool())
    }
    /** TODO: Add bitwise ops ?
    it("should return type UInt for UInt inputs") {
      implicit val scope = (new Symtab())
      assertValid(And(1, 0), UInt())
      assertValid(Or(0xFFFFF, 127), UInt())
      assertValid(Not(0))
    }
    */
    it("should give an error for mismatched input types") {
      implicit val scope = (new Symtab())
      assertErr(0 && True)
      assertErr(False || 1)
    }
    it("should give an error for a non-Bool(), non-Int type") {
      implicit val scope = Symtab(Map('x -> Record(LoInt())))
      assertErr(Not('x))
      assertErr('x && 1)
    }
  }

  describe("The Mux() operator") {
    it("should return a result of the same type as its children") {
      val expr = Mux(Const(1) < 7, 5, 6)
      Given("valid code "+expr)
      val loType = (new Symtab())(expr).loType
      assert(loType.nonConst === UInt())
      Then("that should be of type UInt")
      val expr2 = Mux(Equal(2,3),  True, False)
      Given("valid code "+expr2)
      val loType2 = (new Symtab())(expr2).loType
      assert(loType2.nonConst === Bool())
      Then("that should be of type Bool()")
    }
    it("should fail when the condition is not a Bool()") {
      val badCond = Mux(0, 1, 5)
      Given("bad code "+badCond)
      val errs = (new Symtab()).exprChecker(badCond).left.get
      val err = reduceNewline(errs.map(_.err))
      Then("that should fail with an error:\n"+indent(err))
    }
  }

  describe("Record expressions") {
    it("should allow the extraction of fields from a URec") {
      val RecType = Record(LoInt(), Bool(), UInt())
      val scope = Symtab(Map('r -> RecType))
      Given(s"Value ${'r} of type $RecType")
      RecType.fields.zipWithIndex map {
        case (Record.Field(loType, _), i) => {
          val e = UField('r, i)
          Then(s"Field $i should have type $loType")
          scope.exprChecker(e) match {
            case Left(errs) => {
              val err = reduceNewline(errs.map(_.err))
              throw new AssertionError(err)
            }
            case Right(fieldType) => {
              val errMsg = s"\t${'r}($i) => ${fieldType.loType}; should be $loType\n"
              assert(fieldType.loType === loType, errMsg)
            }
          }
        }
      }
    }
  }

  describe("Range expressions") {
    val scope = Symtab(Map(
      'auu -> Arr(Record(UInt(), UInt())),
      'u -> UInt(),
      'ur -> Record(Bool(), Bool()),
      'b -> Bool()))

    it("should give the correct result type of Range() and LVRange()") {
      def makeTest(lv: LValue, t: LoType) {
        val rlv = BitRange(lv, 3, 1)
        val lvrlv = LVRange(lv, 1, 3)
        
        Given(s"a well-formed Range() expression $rlv of type $t")
        val rlvResType = scope.exprChecker(lv).right.get.loType
        Then(s"that should type-check")
        assert(rlvResType === t, s"result type $rlvResType != $t")
        And(s"the result should have type $t.")

        Given(s"a well-formed LVRange() expression $lvrlv of type $t")
        val lvrlvResType = scope.exprChecker(lv).right.get.loType
        Then(s"that should type-check")
        assert(lvrlvResType === t, s"result type $lvrlvResType != $t")
        And(s"the result should have type $t.")
      }

      makeTest('auu, Arr(Record(UInt(), UInt())))
      makeTest('u, UInt())
      makeTest('auu, Arr(Record(UInt(), UInt())))
    }

    def makeFailTest(e: Expr) {
      Given(s"a malformed [LV]Range() expression $e")
      val errs = scope.exprChecker(e).left.get
      val err = indent(reduceNewline(errs.map(_.err)))
      Then(s"that should should result in errors:\n"+err)
    }

    it("should give an error when the range head is not Range()-able") {
      makeFailTest('ur.range(0, 1))
      makeFailTest('b.range(0, 1))
    }

    it("should give an error when the start or end is not int-valued") {
      makeFailTest('u.range(0, True))
      makeFailTest('auu.range(False, 1))
    }
  }

  describe("Miscellany") {
    it("should allow NumEntries() only for exprs of LoContainerType") {
      val scope = Symtab(
        Map(
          'x -> Record(UInt(), Bool()),
          'y -> Arr(UInt())))
      val scopeStr = indent(scope.altToString, 2)
      Given(s"Symtab ${scopeStr}\n")
      val bad1 = NumEntries(10)
      Given(s"invalid expr $bad1")
      val err1 = reduceNewline(scope.exprChecker(bad1).left.get.map(_.err))
      Then(s"that should fail with error:\n$err1")

      val bad2 = NumEntries('x)
      Given(s"invalid expr $bad2")
      val err2 = reduceNewline(scope.exprChecker(bad2).left.get.map(_.err))
      Then(s"that should fail with error:\n$err2")

      val good1 = NumEntries('y)
      Given(s"valid expr $good1")
      val loType1 = scope(good1).loType
      assert(loType1 === Index(), s"NumEntries() returned type $loType1")
      Then(s"that should type-check, yielding a UInt")
    }

    it("should return an Index() for Size()") {
      val e = Size(UInt())
      Given("size expr "+e)
      val loType = (new Symtab())(e).loType
      assert(loType.nonConst === Index(), s"Type of [$e] is $loType; should be Index")
      Then("That should type-check with Index type")
    }

    it("should return UInt from lower word for valid input types only") {
      val scope = Symtab(Map('x -> Record(LoInt(), LoInt())))
      val good1 = LowerWord(UField('x, 0))
      Given(s"valid expr $good1")
      val loType1 = scope(good1).loType
      assert(loType1 === UInt(), s"LowerWord() yielded $loType1; should be UInt")
      Then(s"that should type-check as a UInt")

      val bad1 = LowerWord('x)
      Given(s"invalid expr $bad1")
      val err = reduceNewline(scope.exprChecker(bad1).left.get.map(_.err))
      Then(s"that should generate an error:\n$err")
    }
  }
}
      
