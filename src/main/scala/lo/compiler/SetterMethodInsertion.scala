// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo
import ressort.compiler.cpp
import ressort.util._

/** A special LoRes->C++ translator that instruments structs with setter methods
  * for pointers to arrays.
  *
  * This feature is needed to allow client code to avoid knowing the auto-
  * generated typename given to array fields.
  */
trait SetterMethodInsertion extends LoAstToCppAst {
  override def transTypedef(td: lo.Typedef)
      (implicit ast: lo.TypedLoAst): cpp.StructDec = {
    val cppStructDec = super.transTypedef(td)
    val setters = for ((id, loType) <- td.fields) yield {
      loType match {
        case lo.Ptr(lo.Arr(t2, _), _) => {
          Some(makeSetter(id, cpp.Array(cpp.CppType(t2))))
        }
        case _ => None
      }
    }
    val setterMap = (setters.flatten map  { s => (s.name -> s) }).toMap
    cppStructDec.copy(methods = setterMap)
  }

  private def makeSetter(id: lo.Id, cppType: cpp.CppType): cpp.Func = {
    val name = cpp.Id(s"_set_${id.name}")
    val cppId = cpp.Id(id.name)
    val tmpId = cpp.Id(s"__tmp")
    val typeT = cpp.TemplateT("_T")
    val body = {
      cpp.Block(List(
        cpp.Free(cppId),
        cpp.Assign(cppId, cpp.ReinterpretCast(cpp.Ptr(cppType), tmpId))))
    }
    cpp.Func(name, cpp.Void, List(tmpId -> typeT), body, List(typeT))
  }
}
