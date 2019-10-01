// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._

object MergeCommonPredicates {
  def apply(typed: TypedLoAst): TypedLoAst = {
    val newAst = translate(typed.ast)
    TypedLoAst(newAst)
  }

  private def translate(ast: LoAst): LoAst = {
    ast match {
      case Block(stmts) => {
        var res = List[LoAst]()
        var lastIf: Option[IfElse] = None

        def addStmts(stmts: List[LoAst]): Unit = {
          for (s <- stmts) {
            s match {
              case b: Block => addStmts(b.ops)
              case IfElse(cond, o1, Nop) if lastIf.map(_.cond == cond).getOrElse(false) => {
                lastIf = Some(IfElse(lastIf.get.cond, lastIf.get.ifBody + translate(o1), Nop))
              }
              case IfElse(cond, o1, Nop) if lastIf.isEmpty => {
                lastIf = Some(IfElse(cond, translate(o1), Nop))
              }
              case _ if lastIf.nonEmpty => {
                res = lastIf.get :: res
                res = translate(s) :: res
                lastIf = None
              }
              case _ => res = translate(s) :: res
            }
          }
        }
        addStmts(stmts)
        if (lastIf.nonEmpty)
          res = lastIf.get :: res
        Block(res.reverse)
      }
      case _ => ast.replaceAstChildren(ast.astChildren.map(translate))
    }
  }
}
