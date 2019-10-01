package ressort.compiler
import ressort.lo.LoAst
import java.io.PrintWriter

/** "Compiled LoRes Code" (`CCode`) ready for compilation by an external tool.
  *
  * This is strictly a container for the string-based representation
  * of code to be handed off to an actual C/C++ compiler.
  */
abstract class CCode {
  /** Actual code to be compiled by the `BackendCompiler` instance */
  def code: String
  
  /** Type and function prototypes needed to make resulting object file
    * interface with runtime libraries provided by the linker.
    */
  def defs: String

  /** The final `LoRes` code of which this is a translation */
  def loRes: LoAst

  /** Outputs `name`.h and `name`.cc at the path indicated by `prefix`.
    *
    * @param headers contains a list of header names (including `.h`)
    *         for which a `#include <...>` statement will be prepended to the
    *         resulting source.
    */
  def write(prefix: String, name: String, headers: Seq[String]) {
    writeFile(text = defs, path = s"$prefix/$name.h")
    val newCode = {
      val newHeaders = headers ++ Seq("stdint.h", "stdlib.h", "math.h", s"$name.h")
      val includes = newHeaders map { h => s"#include <$h>\n" }
      includes.foldLeft("") { _ + _ } + code
    }
    writeFile(text = newCode, path = s"$prefix/$name.cc")
  }

  private def writeFile(text: String, path: String) {
    val pw = new PrintWriter(path)
    pw.write(text)
    pw.close()
  }
}

/** C++ code representation that assume all code packed into a single header.
  *
  * This class is instantiated by the `LoResCompiler` for final output.
  */
class CppCode(headerCode: String, val loRes: LoAst) extends CCode {
  val defs = headerCode
  val code = ""
}
