package ressort.lo.compiler
import ressort.lo._
import ressort.util._
import org.scalatest.FunSpec
import org.scalatest.GivenWhenThen
import org.scalatest.matchers.ShouldMatchers

class DataflowGraphBuilderSpec extends FunSpec with LoResTester with GivenWhenThen {
//  describe("The FindUsages Expression Transform") {
//    it("Should find symbols in arbitrary expressions") {
//      Given("a declaration block:\n" + bigDecBlock.tabStr(3))
//      val ta = Checker(bigDecBlock)
//      val sa = sid(a, ta.scope)
//      val sb = sid(b, ta.scope)
//      val sc = sid(c, ta.scope)
//      val sd = sid(d, ta.scope)
//      val e1 = (a + 1) * (b - c)
//      And(s"An expression $e1")
//      val u1 = FindUsages(List(e1), ta.scope)
//      val corr1 = Set(sa, sb, sc)
//      assert(u1 === corr1)
//      Then(s"It should find usages $u1")
//    }
//
//  }

  describe("Dataflow Graph Construction") {
//    it("Should find all ScopedSyms when building a dataflow graph") {
//      Given("A loop \n"+forLoop.tabStr(3))
//      val ta = Checker(bigDecBlock + forLoop)
//      val usages = FindUsages(ta)
//      And(s"Usages $usages")
//      val dg = AstDataflowGraph(ta)
//      Then("BuildDataflowGraph() should make a seenBy table for it:\n"+dg.seenBy.tableStr(3))
//      val decSet = (dg.seenBy.table.origSymNames).foldLeft(Set[SymLike]()) { _ + _ }
//      val unused = Set(c, d, i)
//      assert(decSet === (usages ++ unused))
//      val sc = sid(c, ta.scope)
//      And("The set of keys in that map should be equal to the usages set plus the unused variables.")
//      assert(dg.seenBy(sc) === Set[ScopedSym]())
//      And(s"$sc should not be seen by anything")
//    }

    it("Should add all symbols from a loop bound to the sensitivity lists of all symbols updated in the body") {
      Given("A loop \n"+bigBoundForLoop.tabStr(3)+"\nwith a complex bound")
      val ta = TypedLoAst(bigDecBlock + bigBoundForLoop)
      val sa = sid(a, ta.scope)
      val sb = sid(b, ta.scope)
      val sc = sid(c, ta.scope)
      val sd = sid(d, ta.scope)
      val dg = AstDataflowGraph(ta)
      Then("It should build a dataflow graph for that:\n"+dg.seenBy.tableStr(3))
      assert(dg.seenBy(sb).contains(sa), s"seenBy($sb) doesn't contain $sa")
      assert(dg.seenBy(sd).contains(sa), s"seenBy($sd) doesn't contain $sa")
      assert(!dg.seenBy(sc).contains(sa), s"seenBy($sc) contains $sa")
      And(s"The seen-by sets for $sb and $sd should contain $sa")
      And(s"The seen-by set for $sc should NOT contains $sa.")
    }

    it("Should handle if-else statements appropriately") {
      Given("an if-else block:\n"+ifElse.tabStr(3))
      val ta = TypedLoAst(bigDecBlock + ifElse)
      val sa = sid(a, ta.scope)
      val sb = sid(b, ta.scope)
      val sc = sid(c, ta.scope)
      val sd = sid(d, ta.scope)
      val dg = AstDataflowGraph(ta)
      Then("It should build a dataflow graph for that:\n"+dg.seenBy.tableStr(3))
      assert(dg.seenBy(sb).contains(sd), s"seenBy($sb) doesn't contain $sd")
      assert(dg.seenBy(sc).contains(sd), s"seenBy($sc) doesn't contain $sd")
      assert(dg.seenBy(sa).contains(sd), s"seenBy($sa) doesn't contain $sd")
      assert(dg.seenBy(sb).contains(sa), s"seenBy($sb) doesn't contain $sa")
      assert(dg.seenBy(sc).contains(sa), s"seenBy($sc) doesn't contain $sa")
      assert(!dg.seenBy(sa).contains(sb), s"seenBy($sa) contains $sb")
      assert(!dg.seenBy(sd).contains(sa), s"seenBy($sd) contains $sa")
      And("It should be correct.")
    }

    it("Should handle Return statements apporpriately") {
      Given("a function with a return statement:\n"+funcRet.tabStr(3))
      val ta = TypedLoAst(funcRet)
      val dg = AstDataflowGraph(ta)
      Then("It should build a dataflow graph for that:\n"+dg.seenBy.tableStr(3))
    }

    it("should mark control flow into a Printf/Return as visible at the output") {
      Given("for loop with a Printf:\n"+forPrint.tabStr(3))
      val ta = TypedLoAst(bigDecBlock + forPrint)
      val sa = sid(a, ta.scope)
      val sb = sid(b, ta.scope)
      val sc = sid(c, ta.scope)
      val sd = sid(d, ta.scope)
      val dg = AstDataflowGraph(ta)
      val TOP = Symtab.Empty.TopId
      Then("it should build a dataflow graph for that:\n"+dg.seenBy.tableStr(3))
      assert(dg.seenBy(sb).contains(TOP), s"seenBy($sb) doesn't contain $TOP")
      assert(dg.seenBy(sd).contains(TOP), s"seenBy($sd) doesn't contain $TOP")
      assert(dg.seenBy(sc).contains(TOP), s"seenBy($sc) doesn't contain $TOP")
      And("it should mark control flow into Printf as visible at the output")
    }
  }

  describe("Dead ScopedSym detection") {
    it("should mark all IDs as dead when none flow to TOP") {
      val code = bigDecBlock + bigBoundForLoop
      Given("Code with several variables:\n"+code.tabStr(3))
      val ta = TypedLoAst(code)
      val dg = AstDataflowGraph(ta)
      val dce = new DeadCodeEliminator(dg)
      val sa = sid(a, ta.scope)
      val sb = sid(b, ta.scope)
      val sc = sid(c, ta.scope)
      val sd = sid(d, ta.scope)
      val dstr = (dce.deadSyms map { s => "    "+s+"\n" }).foldLeft("") { _ ++ _}
      Then("It should produce a set of dead IDs:\n"+dstr)
      assert(dce.deadSyms.contains(sa))
      assert(dce.deadSyms.contains(sb))
      assert(dce.deadSyms.contains(sc))
      assert(dce.deadSyms.contains(sd))
      And("It should contain a, b, c, and d.")
    }

    it("should mark as visible those IDs seen by a return statement.") {
      Given("a function definition with a return statement\n"+funcRet.tabStr(3))
      val ta = TypedLoAst(funcRet)
      val dg = AstDataflowGraph(ta)
      val dce = new DeadCodeEliminator(dg)
      val dstr = (dce.deadSyms map { s => "    "+s+"\n" }).foldLeft("") { _ ++ _}
      Then("it should produce a set of dead IDs:\n"+dstr)
      assert(dce.deadSyms.isEmpty)
      And("that set should be empty")
    }

    it("should mark dead scoped IDs inside a function body.") {
      val code = funcRetDeadCode
      Given("a function withsome dead IDs:\n"+code.tabStr(3))
      val ta = TypedLoAst(code)
      val dg = AstDataflowGraph(ta)
      val dce = new DeadCodeEliminator(dg)
      val dstr = (dce.deadSyms map { s => "    "+s+"\n" }).foldLeft("") { _ ++ _}
      Then("it should produce a set of dead IDs:\n"+dstr)
      assert(dce.deadSyms.size === 1)
      assert(dce.deadSyms.head.sym === d)
      And("That set should consist only of "+d)
    } 

    it("should mark dead scoped IDs inside a complex function body.") {
      val code = complexDeadCode 
      Given("a function withsome dead IDs:\n"+code.tabStr(3))
      val ta = TypedLoAst(code)
      val dg = AstDataflowGraph(ta)
      val dce = new DeadCodeEliminator(dg)
      val dstr = (dce.deadSyms map { s => "    "+s+"\n" }).foldLeft("") { _ ++ _}
      Then("it should produce a set of dead IDs:\n"+dstr)
      val ids = dce.deadSyms map { sid => sid.sym }
      val corrDead = Set(i, j, d)
      assert(ids === corrDead)
      And("That set should consist only of "+corrDead)
    }
  }
}
