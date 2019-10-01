/* C++ AST extensions for dealing with OpenMP constructs */

package ressort.compiler.cpp
import scala.collection.mutable.HashMap

object OpenMP {
  sealed abstract class Schedule(val name: String) {
    override def toString = s" schedule($name)"
  }
  object Schedule {
    val nameMap = HashMap[String, Schedule](
      Static.name   -> Static,
      Dynamic.name  -> Dynamic,
      Guided.name   -> Guided,
      Runtime.name  -> Runtime,
      Auto.name     -> Auto)

    def apply(s: String): Schedule = {
      if (nameMap.contains(s)) {
        nameMap(s)
      } else {
        throw new Error(
          s"OpenMP schedule '$s' does not exist:\n"+
          ((nameMap map { case (k, v) => s"\t$k\n" }).reduce { _ + _ }))
      }
    }
  }

  case object Static  extends Schedule("static")
  case object Dynamic extends Schedule("dynamic")
  case object Guided  extends Schedule("guided")
  case object Runtime extends Schedule("runtime")
  case object Auto    extends Schedule("auto")

  def setNumThreads(n: Expr): CppAst = {
    CallStmt(Call(Id("omp_set_num_threads"), n :: Nil))
  }

  def getNumThreads: Expr = {
    Call(Id("omp_get_num_threads"), Nil)
  }

  def getNumProcs: Expr = {
    Call(Id("omp_get_num_procs"), Nil)
  }

  def getThreadNum: Expr = {
    Call(Id("omp_get_thread_num"), Nil)
  }

  def critical(body: CppAst): CppAst = {
    Pragma("omp critical", body)
  }

  def parallelFor(loop: For, schedule: Option[Schedule] = None): CppAst = {
    val sched = schedule.map(_.toString) getOrElse ""
    Pragma(s"omp parallel for$sched", loop)
  }

  def parallel(body: CppAst, schedule: Option[Schedule] = None): CppAst = {
    val sched = schedule.map(_.toString) getOrElse ""
    Pragma(s"omp parallel$sched", body)
  }

  def forLoop(loop: For, schedule: Option[Schedule] = None): CppAst = {
    val sched = schedule.map(_.toString) getOrElse ""
    Pragma(s"omp for$sched", loop)
  }
}
