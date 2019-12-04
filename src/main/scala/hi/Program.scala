// See LICENSE.txt
/** HiRes Programs: Syntactic sugar for constructing HiRes programs */
package ressort.hi
import ressort.hi.meta.{MetaOp, MetaOpId, MetaParam, ConcreteParam, Concrete}
import scala.collection.mutable.{ArrayBuffer, HashMap}

sealed trait ProgSym {
  def id: Id
  def :=(o: Operator): Unit
  def :=(o: Operator, fields: Seq[Id]): Unit
  def :=(o: MetaOp): Unit
  //def apply(e: Expr): Operator
  def metaOp: Option[MetaOp]
}

class Program {
  private val assigns = ArrayBuffer[Assign]()
  private val symbols = HashMap[String, List[MySym]]()
  private val concrete = HashMap[MetaOpId, ProgSym]()
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

  def rename(id: MetaOpId, sym: ProgSym): Unit = {
    concrete(id) = sym
  }

  def reset(id: MetaOpId): Unit = {
    concrete -= id
  }
  
  private val program = this

  private class MySym(val id: Id) extends ProgSym {
    var metaOp: Option[MetaOp] = None

    def :=(o: Operator, fields: Seq[Id]): Unit = {
      o match {
        case i: IdOp =>
          assigns += Assign(i.id, IdOp(i.id))
        case _ =>
      }
      assigns += Assign(id, o)
      metaOp = Some(Concrete(o, fields, name = Some(this)))
    }

    def :=(o: Operator): Unit = { this := (o, Seq[Id]()) }

    def :=(o: MetaOp): Unit = {
      if (concrete.contains(o.id)) {
        metaOp = Some(concrete(o.id).metaOp.get)
        assigns += Assign(id, concrete(o.id))
      } else {
        metaOp = Some(o.concrete(program))
        assigns += Assign(id, metaOp.get.name.get)
      }
    }

    /**
    def apply(e: Expr): Operator = {
      metaOp match {
        case Some(mop) if (mop.name != Some(this)) => mop.asOperator()(e)
        case _ => Eval(IdOp(id), e)
      }
    }
    **/
  }
}
