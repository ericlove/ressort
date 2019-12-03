// See LICENSE.txt
package ressort.lo.compiler
import ressort.compiler.CompilerConfig
import ressort.lo
import ressort.compiler.cpp._

object OmpTranslator  {
  def defaultSchedule: Option[OpenMP.Schedule] = None
  def ompLoopTranslator() = new OmpLoopTranslator(defaultSchedule)
  def ompArrOpTranslator() = new CppArrOpTranslator()
  def ompLoAstToCppAst =
    new LoAstToCppAst(
      arrOpTranslator = ompArrOpTranslator(),
      loopTranslator = ompLoopTranslator())

  val ompGlobalHeaders = List("omp.h")

  val ompTransforms = List(annotationTransform(_))

  def apply(config: CompilerConfig): LoResCompiler = {
    
    new LoResCompiler(
      globalHeaders = LoResCompiler.defaultGlobalHeaders ++ ompGlobalHeaders,
      transforms = LoResCompiler.defaultTransforms(config) ++ ompTransforms,
      irAstToCppAst = ompLoAstToCppAst)
  }

  /** Transforms the input AST into one where each parallel loop body
    * is annotated with information about any parallel loops that 
    * dominate it.
    */
  private def annotationTransform(tast: lo.TypedLoAst): lo.TypedLoAst = {
    val (fpldAst, dominators) = FindParallelLoopDominators(tast)
    AnnotateParallelLoopBodies(fpldAst, dominators)
  }
}
