package ressort.lo.compiler
import ressort.lo._
import ressort.util

import scala.collection.mutable.{HashMap, HashSet, LinkedHashSet}

/** Performs dead code elimination on an AST using its [[AstDataflowGraph]] */
class DeadCodeEliminator(val dg: AstDataflowGraph, removeUseSym: Boolean=false) {

  def trans(ast: LoAst): LoAst = {
    val newCh = ast.replaceAstChildren(ast.astChildren.map(trans))

    def replaceLValueUpdate(lv: LValue, ast: LoAst): LoAst = {
      val i: Int = AstDataflowGraph.asIndex(lv.root)
      if (isDead(i)) {
        Nop
      } else {
        ast
      }
    }

    val newAst = newCh match {
      case d: DecLike => replaceLValueUpdate(d.sym, newCh)
      case u: LValueUpdate  => replaceLValueUpdate(u.lhs, newCh)
      case u: UseSym if removeUseSym => Nop
      case u: UseSym => replaceLValueUpdate(u.observer, newCh)
      case b: Block =>  {
        val innerNops = b.ops map { _ == Nop }
        if (innerNops.foldLeft(true) { _ && _ })
          Nop
        else
          Block(b.ops filter { _ != Nop })
      }
      case f: ForLoopLoAst  => if (f.body == Nop) Nop else f
      case w: While => if (w.body == Nop) Nop else w
      case i: IfElse => if (i.ifBody == Nop && i.elseBody == Nop) Nop else i
      case _ => newCh
    }

    val finalAst = newAst match {
      case Assign(l, e) if l == e => Nop
      case Assign(l, FakeUse(e)) if l == e => Nop
      case _ => newAst
    }

    finalAst
  }

  /** Whether each int-sym (identified by index) has been marked dead yet */
  private val isDead: Array[Boolean] = {
    val numSyms = dg.origSymNames.length
    val isDead_ = Array.fill[Boolean](numSyms)(true)


    // For each symbol in `origSymNames`, a list of symbols it sees
    // (i.e. just invert the original "seen-by" graph into a "sees" graph)
    val sees = Array.fill[List[Integer]](numSyms) { List[Integer]() }
    for ((set, i) <- dg.seenBy.table.zipWithIndex) {
      set.map(sees(_) ::= i)
    }

    // Walk the "sees" graph from the output and mark all reachable nodes as alive
    var frontier = List[Integer](AstDataflowGraph.TopIntId)
    while (frontier.nonEmpty) {
      var next = List[Integer]()
      for {
        i <- frontier
        j <- sees(i)
      } yield {
        if (isDead_(j)) {
          next ::= j
          isDead_(j) = false
        }
      }
      frontier = next
    }

    // Don't include AstDataflowGraph.TopIntId in the dead set
    isDead_(AstDataflowGraph.TopIntId) = false
    isDead_
  }

  lazy val deadSyms: Set[ScopedSym] = isDead.zipWithIndex.filter(_._1).map(_._2).map(dg.seenBy.invertedRename).toSet
}

object DeadCodeEliminator {
  def apply(ta: TypedLoAst, removeUseSym: Boolean=false): TypedLoAst = {
    val dg = AstDataflowGraph(ta)
    val dce = new DeadCodeEliminator(dg, removeUseSym)
    val newAst = dce.trans(dg.ast)
    val finalAst = dg.withOrigSyms(newAst)
    // Re-typecheck the new AST, in case there are any mismatched scopes
    // produced during AST manipulation
    TypedLoAst(finalAst)
  }
}