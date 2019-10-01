// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo
import ressort.compiler.cpp._

/** OpenMP-specific C++ for loop translation
  *
  * @note Assumes that the [[ressort.lo.compiler.FindParallelLoopDominators]] and
  *       [[ressort.lo.compiler.AnnotateParallelLoopBodies]] transforms have been applied!
  */
class OmpLoopTranslator(
      schedule:       Option[OpenMP.Schedule]) 
    extends CppLoopTranslator {

  def transLoopWithoutAnnotation(fp: lo.ForPar)
      (implicit ast: lo.TypedLoAst,
        irAstToCppAst: LoAstToCppAst): CppAst = {
    val (serialLoop, decs) = transSerialFor(fp)

    Block(List(decs, serialLoop))
  }

  def transLoopWithAnnotation(fp: lo.ForPar, alb: AnnotatedLoopBody)
      (implicit ast: lo.TypedLoAst,
        irAstToCppAst: LoAstToCppAst): CppAst = {
    val (serialLoop, decs) = transSerialFor(fp)

    if (alb.dominators.isEmpty) {
      Block(
        List(
          Nop,//OpenMP.setNumThreads(OpenMP.getNumProcs),
          decs,
          OpenMP.parallel(
            OpenMP.forLoop(serialLoop, schedule))))
    } else {
      transLoopWithoutAnnotation(fp)
    }
  }


  def transForSeq(f: lo.ForSeq)
      (implicit ast: lo.TypedLoAst,
        irAstToCppAst: LoAstToCppAst): CppAst = {
    val (serialLoop, decs) = transSerialFor(f)

    Block(List(decs, serialLoop))
  }
  
  def transForPar(fp: lo.ForPar)
      (implicit ast: lo.TypedLoAst,
        irAstToCppAst: LoAstToCppAst): CppAst = {
    fp.body match {
      case alb: AnnotatedLoopBody => transLoopWithAnnotation(fp, alb)
      case other => transLoopWithoutAnnotation(fp)
    }
  }

  /** Translates [[ressort.lo.ForLoopLoAst]]s
    *
    * The OpenMP for loop translator handles parallel and sequential
    * LoRes loops differently by using [[ressort.lo.OpenMP.parallelFor]] to emit
    * parallel code for [[ressort.lo.ForPar]] loops.
    */
  override def translate(f: lo.ForLoopLoAst)
      (implicit ast: lo.TypedLoAst,
        irAstToCppAst: LoAstToCppAst): CppAst = {
    f match {
      case s: lo.ForSeq => transForSeq(s)
      case p: lo.ForPar => transForPar(p)
    }
  }
}
