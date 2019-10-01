// See LICENSE.txt
package ressort.lo.compiler
import ressort.lo._
import ressort.hi.compiler.HiResCompiler.CompiledLoRes
import scala.collection.mutable.{HashSet, LinkedHashMap, LinkedHashSet}


/** LoRes Code split into separate code and definitions.
  *
  * This is equivalent to [[ressort.lo.compiler.SplitLoRes]] but
  * for situations where type checking is desired.
  */
case class TypedSplitLoRes(defs: TypedLoAst, code: TypedLoAst)

/** Untyped LoRes Code split into separate code and definitions.
  *
  * Some translator targets (especially those based on C++) will
  * want to generate separate files that declare interfaces, types
  * and function prototypes, so `TypedSplitLoRes` provides for that separation
  * as an explicit part of the translation process.
  */
case class SplitLoRes(defs: LoAst, code: LoAst) {
  lazy val typed: TypedSplitLoRes = {
    val typedDefs = TypedLoAst(defs)
    val typedCode = TypedLoAst(code, external = Some(typedDefs.globals))
    TypedSplitLoRes(defs = typedDefs, code = typedCode)
  }
}

object SplitLoRes {
  /** Generates a proper [[ressort.lo.compiler.SplitLoRes]] for any AST.
    *
    * The resulting [[ressort.lo.compiler.SplitLoRes]] will have topologically
    * ordered [[ressort.lo.Typedef]]s for each top-level (outside of a function)
    * type encountered in `ast`.
    */
  def apply(ast: LoAst): SplitLoRes = {
    val (code, types) = getTypedefs(ast)
    val defs = orderedTypedefs(types)
    SplitLoRes(defs = defs, code = code)
  }

  /** Finds all necessary top-level type definitions and removes them from the AST.
    *
    * Extracts all top-level [[ressort.lo.Typedef]]s from the given AST and
    * generates a new one without them, and a set of all typedefs. If there is
    * a [[ressort.lo.Struct]] type without an explicit typedef, one will be
    * generated.
    */
  private def getTypedefs(ast: LoAst): (LoAst, Set[Typedef]) = {
    val types = HashSet[Typedef]()

    // Walk the fields of a Typedef in case there are any structs without
    // an explicit typedef (and generate one for them)
    def typedefStructs(t: LoType) {
      t match {
        case s: Struct => {
          types += Typedef(s)
          s.fields.map(_._2).map(typedefStructs)
        }
        case Ptr(t2, _) => typedefStructs(t2)
        case s: Scalar =>
        case Arr(t2, _) => typedefStructs(t2)
        case d: Data => typedefStructs(d.scalarType)
        case _ =>
      }
    }

    def walkAst(ast: LoAst): LoAst = {
      val newAst = ast match {
        case t: Typedef => {
          types += t
          t.fields.map(_._2).map(typedefStructs)
          Nop
        }
        case d: Dec => { typedefStructs(d.loType); d }
        case da: DecAssign => { typedefStructs(da.loType); da }
        case Block(stmts) => {
          Block(stmts.map(walkAst).filter(_ != Nop))
        }
        case _ => ast.replaceAstChildren(ast.astChildren.map(walkAst))
      }
      newAst
    }
    val newAst = walkAst(ast)
    (newAst, types.toSet)
  }

  /** Returns an AST with the typedefs in `typedefs` topologically ordered. */
  private def orderedTypedefs(typedefs: Set[Typedef]): LoAst = {
    // First, build a table of all `Typedef`s, and remove them from the AST
    val typeMap = LinkedHashMap[Id, Typedef]()
    for (td <- typedefs) {
      typeMap += (td.name -> td)
    }
    val typedefsLeft = HashSet[Typedef]()
    typedefsLeft ++= typedefs

    // Then, build a topological ordering of typedefs by removing
    // successive dependencies from `typedefsLeft` until no dependencies remain
    val ordered = LinkedHashSet[Typedef]()
    def addTypedef(typedef: Typedef) {
      typeMap -= typedef.name
      typedefsLeft -= typedef
      if (!ordered.contains(typedef)) {
        ordered += typedef
      } 
    }

    while (typedefsLeft.nonEmpty) {
      val next = typedefsLeft.head
      def walkTypedef(td: Typedef) {
        def walkType(t: LoType) {
          t match {
            case TypeRef(name, _) if !typeMap.contains(name) => typeMap.get(name).map(walkTypedef)
            case s: Struct => walkTypedef(Typedef(s))
            case Ptr(t2, _) => walkType(t2)
            case s: Scalar =>
            case Arr(t2, _) => walkType(t2)
            case d: Data => walkType(d.scalarType)
            case _ => 
          }
        }

        for ((id, loType) <- td.fields) {
          walkType(loType)
        }
        addTypedef(td)
      }
      walkTypedef(next)
    }
    Block(ordered.toList)
  }
}

object TypedSplitLoRes {
  /** Extracts a type-checked [[TypedSplitLoRes]] from a [[CompiledLoRes]] */
  def apply(cop: CompiledLoRes): TypedSplitLoRes = {
    val defs = TypedLoAst(cop.defs)
    //println("FAILING CODE:\n"+cop.func.tabStr(3))
    val code = TypedLoAst(cop.func, external = Some(defs.globals))
    TypedSplitLoRes(defs, code)
  }

  /** Separates typedefs from main code so they can be put in a header */
  def apply(ast: TypedLoAst): TypedSplitLoRes = {
    SplitLoRes(ast.ast).typed
  }
}
