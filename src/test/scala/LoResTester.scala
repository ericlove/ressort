package ressort.lo.compiler
import ressort.lo._
import ressort.util._

/** Defines [[Id]]s and [[LoAst]]s useful for many Lo/transform tests */
trait LoResTester {
  val a = Id("a")
  val b = Id("b")
  val c = Id("c")
  val d = Id("d")
  val i = Id("i")
  val j = Id("j")

  val forLoop = {
    ForBlock(i, b, 
      (a := a * i))
  }

  val bigBoundForLoop = {
    ForBlock(i, b * (d + 1),
      (a := a * i))
  }

  val forPrint = {
    ForBlock(i, b * d,
      (Printf("c + i: %d\n", c + i)))
  }

  val bigDecBlock = {
    DecAssign(a, Index(), Const(0)) +
    DecAssign(b, Index(), Const(10)) + 
    DecAssign(c, Index(), Const(20)) + 
    DecAssign(d, Index(), Const(30)) +
    DecAssign(i, Index(), Const(0))
  }

  val ifElse = {
    IfElse(a > (b + c),
      a := Const(1),
      d := a)
  }

  val funcRet = {
    FuncDec(a, List(b -> Index()),
      DecAssign(c, Index(), Const(20)) +
      Return(c * b),
    Some(Index()))
  }

  val funcRetDeadCode = {
    FuncDec(a, List(b -> Index()),
      DecAssign(c, Index(), Const(20)) +
      DecAssign(d, Index(), c) +
      Return(c * b),
    Some(Index()))
  }

  val complexDeadCode = {
    FuncDec(a, List(b -> Index()),
      DecAssign(c, Index(), Const(20)) +
      DecAssign(d, Index(), c) +
      DecAssign(j, Index(), Const(0)) +
      ForBlock(i, d,
        (j := j + b)) +
      Return(c * b),
    Some(Index()))
  }

  def sid(id: Id, scope: Symtab): ScopedSym = {
    ScopedSym(id, scope.getEnclosing(id))
  }
}
