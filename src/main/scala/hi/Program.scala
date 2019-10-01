// See LICENSE.txt
/** HiRes Programs: Syntactic sugar for constructing HiRes programs */
package ressort.hi
import ressort.hi.meta.{MetaOp, MetaParam, ConcreteParam}
import scala.collection.mutable.{ArrayBuffer, HashMap}

sealed trait ProgSym {
  def id: Id
  def :=(o: Operator): Unit
  def :=(o: MetaOp): Unit
  def apply(e: Expr): Operator
  def metaOp: Option[MetaOp]
}

class Program {
  private val assigns = ArrayBuffer[Assign]()
  private val symbols = HashMap[String, List[MySym]]()
  val params = HashMap[MetaParam[_], ConcreteParam[_]]()

  def apply(param: MetaParam[_]): ConcreteParam[_] = params(param)

  def setParam(param: MetaParam[_], concrete: ConcreteParam[_]): Unit = {
    params(param) = concrete
  }

  def fresh(name: String): ProgSym = {
    val list = symbols.getOrElse(name, Nil)
    val id = if (list.isEmpty) Id(name) else Id(s"${name}_${list.length}")
    val sym = new MySym(id)
    symbols(name) = sym :: list
    sym
  }

  def apply(o: Operator): Operator = {
    val res = Let(assigns.toList, in = o)
    res
  }
  
  private val program = this

  private class MySym(val id: Id) extends ProgSym {
    var metaOp: Option[MetaOp] = None

    def :=(o: Operator): Unit = {
      assigns += Assign(id, o)
      metaOp = None
    }

    def :=(o: MetaOp): Unit = {
      metaOp = Some(o.concrete(program))
      assigns += Assign(id, metaOp.get.name.get)
    }

    def apply(e: Expr): Operator = {
      metaOp match {
        case Some(mop) => mop.eval(e)
        case None => Eval(IdOp(id), e)
      }
    }
  }
}
