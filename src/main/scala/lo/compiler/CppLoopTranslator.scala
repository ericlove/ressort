// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo
import ressort.compiler.cpp._


/** Performs translation LoRes for loops into C++ loops
  *
  * This class provides utility functions and default implentations
  * of loop translation to be used by different C++ translators. The default
  * implementations are called directly by the [[LoAstToCppAst]] base class.
  */
class CppLoopTranslator {
  import CppLoopTranslator._

  /** Returns constant [[CppForLoopBounds]] for the C++ translation of
    * an LoRes [[lo.ForLoopLoAst]] loop.
    */
  def getConstantLoopBounds(f: lo.ForLoopLoAst)
      (implicit ast: lo.TypedLoAst,
        irAstToCppAst: LoAstToCppAst): ConstantLoopBounds = {
    val (minConst, minConstDec) = {
      irAstToCppAst.constParam(f.min, f.index.name+"_min")
    }
    val (maxConst, maxConstDec) = {
      irAstToCppAst.constParam(f.max, f.index.name+"_max")
    }
    val (strideConst, strideConstDec) = {
      irAstToCppAst.constParam(f.stride, f.index.name+"_stride")
    }
    val decs = {
      val dopt = List(minConstDec, maxConstDec, strideConstDec)
      Block(dopt.flatten)
    }
    ConstantLoopBounds(minConst, maxConst, strideConst, decs)
  }

  /** Returns the type of the C++ translation of the loop index variable of
    * the given [[lo.ForLoopLoAst]].
    */
  def cppIndexType(f: lo.ForLoopLoAst)
      (implicit ast: lo.TypedLoAst,
        irAstToCppAst: LoAstToCppAst): CppType = {
    // For now, all for loops always use size_t
    SizeT(const=false)
  }

  /** Generic serial for loop translation
    *
    * The default [[LoAstToCppAst]] implementation translates both parallel
    * and sequential for loops using this serial for loop routine.
    *
    * @return a pair of consisting of (C++ loop, declarations)
    */
  def transSerialFor(f: lo.ForLoopLoAst)
      (implicit ast: lo.TypedLoAst,
        irAstToCppAst: LoAstToCppAst): (For, CppAst)= {
    val i = Id(f.index.name)
    val body = ast.children(0)
    val bounds = getConstantLoopBounds(f)
    val cppBody = irAstToCppAst.trans(ast.children(0))
    val indexType = cppIndexType(f)

    val loop = {
      For(
        Dec(i, indexType, Some(bounds.min)),
        Lt(i, bounds.max),
        Assign(i, Plus(i, bounds.stride)),
        cppBody)
    }

    (loop, bounds.decs)
  }

  def translate(f: lo.ForLoopLoAst)
      (implicit ast: lo.TypedLoAst,
        irAstToCppAst: LoAstToCppAst): CppAst = {
    // The default implementation is to emit a simple serial loop.
    val x = transSerialFor(f)
    Block(List(x._2, x._1))
  }
}


object CppLoopTranslator {
  /** Represents a C++ for loop with constant expression bounds,
    * as well as C++ code to declare and initialize them.
    */
  case class ConstantLoopBounds(
      min: Expr,
      max: Expr,
      stride: Expr,
      decs: CppAst)
}  
