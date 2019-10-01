// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._
import ressort.util
import scala.collection.mutable.HashMap

class RemoveUnusedPointers(ast: LoAst) {
  val used = HashMap[SymLike, Boolean]()

  def walk(ast: LoAst): Unit = {
    def walkExpr(e: Expr): Unit = e match {
      case s: SymLike if used.contains(s) => used(s) = true
      case _ => e.children.map(walkExpr)
    }
    ast.astChildren.map(walk)
    ast match {
      case Dec(sym, Ptr(_, _)) => {
        used(sym) = false
        ast.exprChildren.map(walkExpr)
      }
      case DecAssign(sym, Ptr(_, _), _) => {
        used(sym) = false
        ast.exprChildren.tail.map(walkExpr)
      }
      case Assign(sym: SymLike, _) if used.contains(sym) => {
        ast.exprChildren.tail.map(walkExpr)
      }
      case _ => ast.exprChildren.map(walkExpr)
    }
  }

  private def transform(ast: LoAst): LoAst = {
    ast.replaceAstChildren(ast.astChildren.map(transform)) match {
      case Dec(sym, _) if !used.getOrElse(sym, true) => Nop
      case Assign(lv, _) if !used.getOrElse(lv.root, true) => Nop
      case Block(Nop::Nil) => Nop
      case b: Block => Block(b.ops.filter(_ != Nop))
      case other => other
    }
  }

  lazy val newAst: LoAst = {
    walk(ast)
    transform(ast)
  }
}

object RemoveUnusedPointers {
  def apply(typed: TypedLoAst): TypedLoAst = {
    val rup = new RemoveUnusedPointers(typed.ast)
    TypedLoAst(rup.newAst)
  }
}
