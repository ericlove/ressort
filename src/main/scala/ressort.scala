package ressort
import hi._
import ressort.compiler._
import ressort.hi.compiler.HiResCompiler
import ressort.lo.compiler.{OmpTranslator}

object Ressort {
  def compile(
      operator:     Operator,
      funcType:     Func, 
      config:       CompilerConfig=CompilerConfig.DefaultConfig,
      verbose:      Boolean=false,
      name:         Option[String]=None): CppCode = {
    val fc = new HiResCompiler()(config)
    val trans = OmpTranslator()

    val lo = fc.compile(operator, funcType, verbose, name)
    val ccCode = trans.translate(lo)

    ccCode
  }
}
