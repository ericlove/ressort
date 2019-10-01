package ressort.lo
import ressort.util._
import scala.collection.mutable.HashMap

/** Uniquely identifies a LoRes symbol as a tuple with its defining scope. */
case class ScopedSym(sym: SymLike, scope: Symtab)


/** Used throughout the LoRes infrastructure to represent scopes.
  *
  * has various apply() methods that return type-checked expressions.
  * Maintains a hierarchy of mappings of Id -> LoTypes,
  */
class Symtab(
    val parent: Option[Symtab] = None, 
    val returnType: Option[Primitive] = None) {
  private val env = new HashMap[SymLike, LoType]()
  
  /** Returns a list of symtols that are defined by precisely this scope */
  def myScope: Seq[SymLike] = (env map { case (v,t) => v }).toSeq

  /** Returns an alternative string representation of this environment
    * that contains much more useful information for debugging.
    */
  def altToString: String = {
    val envStr = env.map(p => s"\t${p._1} -> ${p._2}").mkString(",\n")
    val myStr = "\n{ " + envStr + "}"
    (parent.map(_.altToString+",") getOrElse "") + myStr
  }

  /** Returns the LoType of given identifier, or none if it is not
    * defined in the current environment.
    */
  def symType(v: SymLike): Option[LoType] = {
    val res = env.get(v) orElse parent.flatMap(_.symType(v))
    res
  }

  /** Returns the Func type of given identifier, or none if it is not 
    * defined in the current environment.
    */
  def typeOfFunc(name: SymLike): Option[Func] = {
    symType(name) match {
      case Some(f @ Func(_, _)) => Some(f)
      case _ => None
    }
  }


  /** Returns the scope in which the given identified is defined,
    * or throws an exception if it is undefined.
    */
  def getEnclosing(v: SymLike): Symtab = {
    if(env contains v)
      this
    else
      parent.get.getEnclosing(v)
  }

  /** Returns a unique identifier for `s` in this context */
  def unique(s: SymLike): ScopedSym = {
    ScopedSym(s, getEnclosing(s))
  }

  /** Returns true iff this is the parent of other, or the parent
    * of another Symtab that dominates(other)
    */
  def dominates(other: Symtab): Boolean = {
    if(other.eq(this)) {
      true
    } else {
      other.parent match {
        case Some(scope) if(scope == this) => true
        case Some(scope) => dominates(scope)
        case None => false
      }
    }
  }

  /** Adds `sym` to this table with the given type */
  def add(sym: SymLike, loType: LoType): Unit = {
    env(sym) = loType
  }

  /** Returns a new [[Symtab]] with this as its parent */
  def child(): Symtab = new Symtab(Some(this), this.returnType)

  // Used to check expressions when it is not yet know that they are
  // well-formed.
  val exprChecker = new ExprChecker(this)

  /** Returns the type of an expression __only__ when it is known a priori
    * that the expression is well-formed (will generate exception otherwise).
    *
    * @returns A [[TypedExpr]] or throws an exception.
    */
  def apply(e: Expr, lines: Option[LoAstLines]=None): TypedExpr = {
    exprChecker(e, lines) match {
      case Right(texpr) => texpr
      case Left(errs) => {
        val estr = indent(reduceNewline(errs.map(_.err)), 3)
        throw new AssertionError(estr)
      }
    }
  }

}

object Symtab {
  def apply(map: Map[SymLike, LoType]): Symtab = {
    val tab = new Symtab()
    map.map(p => tab.add(p._1, p._2))
    tab
  }
  /** Represents the innermost, empty symbol table */
  object Empty extends Symtab {
      override def symType(v: SymLike) = v match { 
        case _ => None
      }
      override def altToString = "[Empty]"
      override def toString() = altToString

      /** Singleton [[ScopedSym]] that represents a universal data sink --
        * that is, anything that writes to this is considered to be
        * visible in the program's output.
        */
      val TopId = ScopedSym(Id("__TOP__"), this)
  }
}
