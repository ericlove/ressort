// See LICENSE.txt
package ressort.lo.compiler
import ressort.compiler.cpp
import ressort.compiler.CppCode
import ressort.hi.compiler.HiResCompiler.CompiledLoRes
import ressort.lo.compiler._
import ressort.lo
import ressort.lo.TypedLoAst
import ressort.hi
import ressort.util._
import scala.collection.mutable.LinkedHashMap


/** Converts intermediate LoRes code into C++ code for final compilation.
  *
  * Ressort generates a header file for each compiled kernel containing:
  *   - All necessary typedefs for intermediate data formats
  *   - A single C++ class with a canonical name (see `className`)
  *   - A constructor for that class that pre-allocates necessary buffers
  *   - Getter and setter methods for arguments to the kernel, which must be
  *     set prior to execution, and with names beginning `_set`.
  *   - An `_run()` method to execute the kernel, called after all setters.
  *
  * @param globalHeaders  Header files to include via `#include <[name]>`
  * @param localHeaders   Header files to include via `#include "[name]"`
  * @param irAstToCppAst An AST converter appropriate for the desired target.
  *                       Invoked after all `LoRes`-level transformations applied.
  */
class LoResCompiler(
    val globalHeaders: Seq[String] = LoResCompiler.defaultGlobalHeaders,
    val localHeaders: Seq[String] = LoResCompiler.defaultLocalHeaders,
    val transforms: Seq[lo.TypedLoAst => lo.TypedLoAst] = LoResCompiler.defaultTransforms,
    val irAstToCppAst: LoAstToCppAst = LoResCompiler.defaultLoAstToCppAst) {

  /** Method that clients should call to obtain C++ code for supplied LoRes */
  def translate(cop: CompiledLoRes): CppCode = {
    val newFunc = fakeClassFunc(cop, allocateFields(cop.func.params))

    val xir = {
      val split = SplitLoRes(cop.defs + newFunc)
      val typed = lo.TypedLoAst(split.defs + split.code)
      TypedSplitLoRes(applyTransforms(typed))
    }

    val (runFunc, constructor) = {
      val (remainder, ctorOpt) = FunctionExtractor(lo.Id(className(cop)), xir.code.ast)
      val (empty, runFuncOpt) = FunctionExtractor(lo.Id(className(cop)), remainder)
      (runFuncOpt.get.toFuncDec, ctorOpt.get)
    }

    val cppCode = {
      val body = {
        val typedLoAst = lo.TypedLoAst(xir.defs.ast + runFunc)
        val cppFunc = irAstToCppAst.trans(typedLoAst)
        def extractFunc(ast: cpp.CppAst): Option[cpp.Func] = {
          ast match {
            case f: cpp.Func => Some(f)
            case b: cpp.Block => {
              for (stmt <- b.body) {
                extractFunc(stmt).map(s => return Some(s))
              }
              None
            }
            case _ => None
          }
        }
        lazy val cppLines = cppFunc.lines.mkString("\n")
        val f = extractFunc(cppFunc).getOrElse(
          throw new Error(s"Shouldn't have returend non-func ${cppLines} as _run()"))
        f.body
      }
      val run = cpp.Func(cpp.Id("_run"), cpp.CppType(runFunc.returnType.get), List(), body)
      val fields = constructor.params map { case (id, loType) =>
        (cpp.Id(id.name) -> cpp.CppType(loType))
      }
      val cppConstructor = {
        val cppFunc = irAstToCppAst.trans(lo.TypedLoAst(constructor))
        cppFunc match {
          case f: cpp.Func => f.body
          case _ => {
            throw new Error(s"Shouldn't have returned non-func $cppFunc as constructor")
          }
        }
      }
      cpp.ClassDec(
        cpp.Id(className(cop)),
        fields,
        List(run.name -> run),
        cppConstructor) 
    }

    val header = {
      s"""
      |#ifndef RESSORT_AUTOGEN_H
      |#define RESSORT_AUTOGEN_H
      |
      |$includeString
      |
      |${reduceNewline(irAstToCppAst.trans(xir.defs).lines)}
      |${reduceNewline(cppCode.lines)}
      |
      |#endif // #ifndef RESSORT_AUTOGEN_H
      """.stripMargin
    }
    new CppCode(header, xir.defs.ast + runFunc)
  }


  /** Returns a string of C++ `#include` statements */
  final def includeString: String = {
    val gs = globalHeaders map { h => s"#include <$h>" }
    val ls = localHeaders map { h => s"""#include "$h" """ }
    reduceNewline(gs ++ ls)
  }



  /** Returns a [[ressort.cpp.CppAst]] containing prototypes of all functions in `code` */
  def getPrototypes(code: cpp.CppAst): cpp.CppAst = {
    val protos: Seq[cpp.FuncPrototype] = LoResCompiler.getPrototypes(code)
    cpp.Block(protos.toList)
  }

  /** Canonical format for operator class names. */
  private def className(cop: CompiledLoRes): String = {
    s"Ressort_${cop.func.name.name}"
  }

  /** Returns a FuncDec that fakes a "class" using parameters as a namespace */
  private def fakeClassFunc(cop: CompiledLoRes, constructor: lo.LoAst): lo.FuncDec = {
    val name = lo.Id(className(cop))
    val xtor = lo.FuncDec(
      name = name,
      params = cop.func.params,
      returnType = None,
      body = constructor)
    lo.FuncDec(
      name = name,
      params = cop.func.params,
      returnType = cop.func.returnType,
      body = xtor + cop.func.body)
  }
    
  /** Returns a block of allocations for each array in the map `params`
    *
    * We use this to generate a constructor prior to transformation passes.
    * Each array is of length zero, as _base_ array allocations should later
    * be removed (so that pointers can instead be set to input buffers).
    */
  private def allocateFields(fields: Seq[(lo.Id, lo.Primitive)]): lo.LoAst = {
    import lo._
    val allocs = for ((id, prim) <- fields) yield {
      def alloc(lv: LValue, loType: LoType): List[LoAst] = {
        loType match {
          case Ptr(Arr(t, _), _) => {
            HeapAlloc(id, Some(Const(0))) :: alloc(id.sub(Const(0)), t)
          }
          case Ptr(Struct(_, fields, _), _) => {
            (fields map { case (id, loType) => alloc(lv.dot(id), loType) }).toList.flatten
          }
          case _=> Nil
        }
      }
      alloc(id, prim)
    }
    Block(allocs.toList.flatten)
  }

  /** Applies the transforms listed in [[transforms]] to the input `TypedSplitLoRes` */
  def applyTransforms(ast: TypedLoAst): TypedLoAst = {
    transforms.foldLeft(DeadCodeEliminator(ast)) { case (i, x) => x(i) }
  }
}


object LoResCompiler {
  val defaultGlobalHeaders = Seq("stdint.h", "string.h", "array", "math.h", "tpch.h")
  val defaultLocalHeaders = Seq[String]()
  val defaultLoAstToCppAst = new LoAstToCppAst()
  def printAst(typed: lo.TypedLoAst): lo.TypedLoAst = {
    println(UniqueSymbolNames(typed).ast.tabStr(0))
    println()
    println()
    typed
  }
  val defaultTransforms: List[lo.TypedLoAst => lo.TypedLoAst] = {
    List(
      RecGroupEliminator(_), // mandatory
      RecStructs(_), // mandatory
      UnpackScalarStructs(_),
      UnpackScalarStructs(_),
      DeadCodeEliminator(_),
      StaticSingleAssignment(_),
      PropagateConstants(_),
      DeadCodeEliminator(_),
      // Okay to const-prop inside Phi() after DCE, but not before
      CommonSubExpressions(_),
      PropagateConstants(_, true),
      StaticSingleAssignment.collapse(_),
      // Remove `UseSym`s because this is the final DCE
      DeadCodeEliminator(_, true),
      RemoveUnusedPointers(_),
      MergeCommonPredicates(_),
      UniqueSymbolNames(_))
  }

  /** Separate all [[StructDec]]s from the top of C++ code so they
    * may be emitted separately in a header file to be shared
    * with external code.
    */
  def separateStructs(stmt: cpp.CppAst): (cpp.CppAst, Seq[cpp.StructDec]) = {
    def separateStructsHelper(
      stmt: cpp.CppAst,
      sds: Seq[cpp.StructDec]): (cpp.CppAst, Seq[cpp.StructDec]) = {
      stmt match {
        case cpp.Block(stlist) => stlist match {
          case h::t => { 
            val pairs = stlist map { 
              stmt => separateStructsHelper(stmt, Seq[cpp.StructDec]())
            }
            val newStmts = (pairs map { _._1 }).foldLeft(List[cpp.CppAst]()) {
              _ ++ List(_) 
            }
            val newSds = (pairs map { _._2 }).foldLeft(Seq[cpp.StructDec]()) { 
              _ ++ _
            }
            (cpp.Block(newStmts), newSds)
          }
          case _ => (cpp.Nop, Seq())
        }
        case sd @ cpp.StructDec(_,_,_) => (cpp.Nop, sds++Seq(sd))
        case other => (other, Seq())
      }
    }
    separateStructsHelper(stmt, Seq())
  }

  /** Create prototypes for all top-level functions defined in the C++ code
    * so they can be emitted into the header file for use by external code.
    */
  def getPrototypes(stmt: cpp.CppAst): Seq[cpp.FuncPrototype] = stmt match {
    case cpp.Block(h::Nil) => getPrototypes(h)
    case cpp.Block(h::t) => getPrototypes(h) ++ getPrototypes(cpp.Block(t))
    case cpp.Func(name, retCppType, params, _, templateTypes) => {
      Seq(cpp.FuncPrototype(name, retCppType, params, templateTypes))
    }
    case _ => Seq()
  }
}

/** Extracts thd function with given `name` from any AST.
  *
  * Used to remove constructors, getters, setters, and the like.
  */
class FunctionExtractor(name: lo.Id) extends lo.compiler.AstTransform {
  type T = Unit

  var func: Option[lo.FuncDec] = None

  def trans(ast: lo.LoAst, children: List[XFormAst]): XFormAst = {
    replaceChildren(ast, children) match {
      case f: lo.FuncDec if (f.name == name && func.isEmpty) => {
        func = Some(f)
        XFormAst(lo.Nop, ())
      }
      case other => XFormAst(other, ())
    }
  }
}


object FunctionExtractor {
  /** Returns the top-level function named `name`, if any, and the AST with it removed */
  def apply(name: lo.Id, ast: lo.LoAst): (lo.LoAst, Option[lo.FuncDec]) = {
    val fe = new FunctionExtractor(name)
    val xfast = fe.dfTrans(ast)
    (xfast.newAst, fe.func)
  }
}
    
