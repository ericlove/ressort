package ressort.hi
import ressort.lo
import ressort.lo.{Record, SplitRecord, FlatRecord}


/** A fully-typed HiRes AST.
  *
  * Each operator represents a function from input relation type to output,
  * so that is explicitly encoded as a [[Func]] in `funcType`.
  * The `children` list contains all sub-ASTs of `o` in syntactic order.
  */
case class TypedHiResOp(
    o: Operator,
    funcType: Func,
    children: List[TypedHiResOp]) {
  override def toString = s"TypedHiResOp($o) : ${funcType.from} -> ${funcType.to}"
}

object TypedHiResOp {
  /** Type-checks `o` and returns a [[TypedHiResOp]] result
    *
    * @throws a TypeCheckError if `o` does not conform to HiRes type rules
    */
  def apply(o: Operator)(implicit env: Map[Id, HiType]): TypedHiResOp = {
    val check = new OperatorTypeCheck(o, env)
    check.typed
  }
}

/** Performs type-checking for a particular [[Operator]] AST.
  *
  * All reported errors of interior [[Operator]] nodes will be described
  * as part of the higher-level operator `o`.
  *
  * @param externalEnv All symbols defined by the outside environment, only some of
  *                     which may be included in the final function type.
  */
private class OperatorTypeCheck(o: Operator, externalEnv: Map[Id, HiType]) {
  lazy val typed: TypedHiResOp = {
    val listing = o.listing(0, OperatorListing.lineLength)
    listing.lines.zipWithIndex map { case (l, i) => l.num = i }
    val ctx = Context(listing, externalEnv)
    checkOperator(ctx)
  }

  /** All the state needed to type-check an expression within an [[Operator]]
    *
    * @param o The current operator being checked
    * @param env The current environment, including any names within a [[Let]]
    * @aparm fields All fields of any record in the current context, such as inside an [[Eval]]
    */
  private case class Context(o: OperatorListing, env: Map[Id, HiType], fields: Seq[Record.Field]=Seq())


  // Arguments are implicit to simplify use of various methods below, such as getType
  private def checkOperator(implicit ctx: Context): TypedHiResOp = {
    // First, recursively compute the types of all Operators used as input to this one
    // and save any Ids they use from their external scope
    val (typedChildren, fromTypes) = ctx.o.ast match {
      case Let(assigns, in) => {
        // handle the case of Let statements separately, since they affect the scope
        var local = Map[Id, Data]()
        var fromTypes = Map[Id, Data]()
        val typedAssigns = for (assign <- ctx.o.children.dropRight(1)) yield {
          val a = assign.ast.asInstanceOf[Assign]
          // Update the toType to produce a named field or record
          implicit val newCtx = ctx.copy(assign.children.head, ctx.env ++ local)
          val init = checkOperator(newCtx)
          val loId = lo.Id(a.id.name)
          def renameScalars(t: HiType): Data = t match {
            case m: MultiHiType => {
              MultiHiType(
                renameScalars(m.head),
                m.tail.map(renameScalars): _*)
            }
            case t: Data => {
              val renamedScalar = t.subVec.withMask(false) match {
                case Payload(n: lo.NonRec) => {
                  NamedPayload(name = a.id, nonRec = n)
                }
                case NamedPayload(_, loType) => NamedPayload(a.id, loType)
                case other => other
              }
              t.withSubVec(renamedScalar).withMask(t.masked)
            }
            case _ => ???
          }
          val typed = {
            val newTo = renameScalars(init.funcType.to)
            init.copy(funcType = init.funcType.copy(to = newTo))
          }
          fromTypes ++= typed.funcType.from
          local = local + (a.id -> typed.funcType.to)
          typed
        }
        implicit val newCtx = ctx.copy(ctx.o.children.last, env = ctx.env ++ local)
        val typedIn = checkOperator(newCtx)
        val typedChildren = typedAssigns :+ typedIn
        (typedChildren, fromTypes -- local.keys)
      }
      case IdOp(id) => {
        (Nil, Map(id -> checkDataExpr(ctx.o.exprChildren.head)))
      }
      case _ => {
        var fromTypes = Map[Id, Data]()
        val childrenFromExprs = {
          var c = List[OperatorListing]()
          def walk(e: ExprListing) {
            c ++= e.operators
            e.ast match {
              // Add a fake IdOp for Id's contained in this expression
              // But only if it's a Length(), which escapes normal scope
              case Length(IdOp(i)) if (ctx.env.contains(i))=> {
                val fake = ExprListing(i, ctx.o.lines, Nil)
                c :+= OperatorListing(IdOp(i), e.lines, Nil, Seq(fake))
              }
              case _ =>
            }
            e.children.map(walk)
          }
          ctx.o.exprChildren.map(walk)
          c
        }
        val typedChildren = for (c <- ctx.o.children ++ childrenFromExprs) yield {
          val typed = checkOperator(ctx.copy(o = c))
          fromTypes ++= typed.funcType.from
          typed
        }
        (typedChildren, fromTypes)
      }
    }

    // Compute output type and check operator/expresison type requirements
    val inputTypes = typedChildren.map(_.funcType.to)
    val toType: Data = ctx.o.ast match {
      case i @ IdOp(id) => checkDataExpr(ctx.o.exprChildren.head)
      case l @ Let(assigns, in) => getType[Data](inputTypes.last, None, "Data")
      case i @ InsertionSort(o2, _) => inputTypes.head
      case m @ MergeSort(o2) => inputTypes.head
      case v @ Eval(o2, e) => {
        val inputType = inputTypes.head
        val fields = inputType.fields
        implicit val newCtx = ctx.copy(fields = fields, env = this.externalEnv)
        val exprType = getScalar(checkDataExpr(ctx.o.exprChildren.head)(newCtx))(newCtx)
        inputType.withSubVec(exprType)
      }
      case h: Histogram => {
        val input = getContainer(inputTypes(0))
        val hist = input.withSubArr(Hist(state = Hist.Built))
        if (!input.hasVec) {
          error(s"Attempting to build histogram from scalar-typed values ($input)")
        }
        ctx.o.exprChildren.map(elist => getHiResInt(checkDataExpr(elist)))
        hist
      }
      case rh: Offsets => {
        val histInput = inputTypes.head
        val reduced = Hist(Hist.Reduced)
        def err(s: Hist.State) = error(s"Attempting to reduce histogram in non-built state (${s})")
        def reduce(d: Data): Data = d match {
          case Hist(Hist.Built) => reduced
          case Hist(s) => err(s)
          case a: Arr => a.copy(reduce(a.t))
          case Chunks(t, _) if !t.hasHistogram => reduced
          case _ => reduced
        }
        reduce(histInput)
      }
      case mr: Partition => {
        val keys = getContainer(inputTypes(0))
        val values = getContainer(inputTypes(1))
        val histInput = inputTypes(2)
        val hist = getHistogram(histInput.subArr)
        if (hist.state != Hist.Reduced) {
          error(
            s"Attempting to move records with histogram in " +
            s"non-reduced state (${hist.state})")
        }
        if (keys.depth != histInput.depth) {
          error(
            s"Moving records with histogram of depth "+
            s"${histInput.depth} and keys of depth ${keys.depth}")
        }
        if (keys.depth != values.depth) {
          error(
            s"Moving records with keys of depth "+
            s"${keys.depth} and values of depth ${values.depth}")
        }
        val newHist = histInput.withSubArr(hist.copy(state = Hist.Moved))
        var valType: Data = values.withMask(false)
        def flatten(a: NestedData): Data = a.base match {
          case n: NestedData => a.withBase(flatten(n))
          case other => other
        }
        if (mr.parallel)
          valType = flatten(valType.toArr)
        val inner = Arr(valType.subArr, histogram = Some(histInput), disjoint=mr.disjoint)
        valType = valType match {
          case f: FlatData => inner
          case n: NestedData => n.withSubArr(inner)
        }
        MultiHiType(valType, newHist)
      }
      case mh: LastArray => {
        val input = getContainer(inputTypes.head)
        def merge(t: Data): Data = t match {
          case Arr(h: Hist, _, _, _, _) => h
          case a: Arr => a.copy(merge(a.t))
          case Hist(_) => error(s"Attempting to merge flat histogram in $input")
          case _ => error(s"Attempting to merge non-histogram type in $input")
        }
        merge(input)
      }
      case rh: RestoreHistogram => {
        val values = getContainer(inputTypes.head)
        val histInput = inputTypes.tail.head
        getHistogram(histInput)
        val arrInput = getArr(inputTypes.head)
        arrInput.innermost match {
          case a: Arr if a.histogram.nonEmpty =>
          case _ => error(s"Innermost array level of input to $rh not a histogram array")
        }
        arrInput
      }
      case ht: HashTable => {
        val input = getContainer(inputTypes(0))
        ht.hash map { hash =>
          val hashInput = getContainer(inputTypes(1))
          checkHash(hashInput.subMask)
        }

        val htbl = Chunks(input.subArr.withMask(false))
        input.withCleanArrays.withSubArr(htbl)
      }
      case hj: HashJoin => {
        val left = getContainer(inputTypes(0))
        val right = getContainer(inputTypes(1))
        val hash = getContainer(inputTypes(2))
        checkHash(hash.subMask)
        hj.test map { test: Expr =>
          val fields = left.fields ++ right.fields
          implicit val newCtx = ctx.copy(fields = fields, env = this.externalEnv)
          val testType = checkDataExpr(newCtx.o.exprChildren.head)(newCtx)
          if (testType != Payload(lo.Bool()))
            error(s"Match test expression $test must be boolean; $testType found.")(newCtx)
        }
        val matchScalar = hj.test match {
          case Some(e) => {
            lo.Record((left.fields ++ right.fields):_*)
          }
          case None => {
            // If no test specified, the 0th fields of each side are treated as keys,
            // and so the right-side's key is elided in the final output type.
            // This saves storage/bandwiwdth in the common case.
            val ltype = left.fields.head.loType
            val rtype = right.fields.head.loType
            if (!ltype.accepts(rtype))
              error(
                s"Implicit equijoin with incompatible types in key: " +
                s"${left.fields.head} has type ${ltype} while ${right.fields.head} has type ${rtype}")
            lo.Record((left.fields ++ right.fields.tail):_*)
          }
        }
        val arr = Chunks(left.subArr.withSubMask(Payload(matchScalar)))
        // Joins are special in that they only add nesting if none exists
        val res = left.withCleanArrays match {
          case a: Arr => a.t.withSubArr(arr)
          case other => other.withSubArr(arr)
        }
        res
      }
      case sp: Operator with Split => {
        getHiResInt(checkDataExpr(ctx.o.exprChildren.head)) // Slices should be an int
        val t = inputTypes.head
        t.withSubArr(Arr(t.subArr, disjoint=sp.disjoint))
      }
      case f: Flatten => {
        val arr = getNested(inputTypes.head)
        try {
          arr.flatten
        } catch {
          case a: AssertionError => error(a.getMessage)
        }
      }
      case c: Compact => {
        val cont = getContainer(inputTypes.head)
        val hist = c.hist.map(_ => inputTypes(1))
        hist.map(getHistogram(_, None))
        cont match {
          case n: NestedData =>
            // TODO: actually should have histogram at _every_ level inside `n`
            n.withCleanArrays.withInnermost(Arr(n.subArr, histogram=(hist)))
          case _ => cont
        }
      }
      case d: DagOp => error(s"DagOp should be used only by the compiler")
      case s: Mask => {
        val input = getContainer(inputTypes(0))
        val cond = getContainer(inputTypes(1))
        getBool(cond.subVec)
        input.withMask(true)
      }
      case c: Collect => {
        val input = getContainer(inputTypes.head)
        input.withMask(false).withNumValid(true)
      }
      case z: Zip => {
        val baseType = {
          val groups = fieldGroups(inputTypes)
          // Name to be filled in by Assign() statement, if any
          val newRec = SplitRecord(groups, None, false)
          Payload(newRec)
        }
        broadcastResultType(baseType, inputTypes)
      }
      case p: Project => {
        val baseType = {
          val groups = fieldGroups(inputTypes)
          // Name to be filled in by Assign() statement, if any
          val newRec = FlatRecord(groups.flatMap(_.fields), None, false)
          Payload(newRec)
        }
        broadcastResultType(baseType, inputTypes)
      }
      case c: Cat => {
        MultiHiType(head = inputTypes.head, tail = inputTypes.tail:_*)
      }
      case u: Uncat => {
        val input = inputTypes.head match {
          case m: MultiHiType if (u.n == 0) => m.head
          case m: MultiHiType => {
            if (u.n > m.tail.length) {
              error(
                s"Attempting to extract ${u.n}th input from " +
                s"${1+m.tail.length}-input parallel-type ${inputTypes.head}")
            }
            m.tail(u.n-1)
          }
          case _ => {
            error(s"Attempting to uncat from non-parallel-type ${inputTypes.head}")
          }
        }
        getType[Data](input, None, "Data")
      }
      case g: Gather => {
        val indices = getContainer(inputTypes(0))
        val target = getContainer(inputTypes(1))
        def err() {
          error(s"Attempting to gather with non-index type ${indices.subVec}")
        }
        indices.subVec match {
					case HiResInt =>
          case p: PayloadLike => p.loType match {
            case lo.Index(_) =>
            case i: lo.IntValued if lo.Index().accepts(i) =>
            case _ => err()
          }
          case _ => err()
        }
        broadcastResultType(target.subVec, Seq(indices, target))
      }
      case p: Position => {
        inputTypes.head.withSubVec(lo.Index())
      }
      case r: Reduction => {
        val input = getContainer(inputTypes.head)
        val newScalar: Scalar = {
          // Compute the result type by making a temporary symbol "id"
          // and combinding it in a scalar expression with itself
          val id = Id("_id")
          val expr = {
            val cexprs = Seq(id, id).map(ExprListing(_, ctx.o.lines, Nil))
            ExprListing( // make a fake one for type checking 
              CommutativeOpExpr(r.op_, id, id),
              ctx.o.lines,
              cexprs)
          }
          val env = Map(id -> input.subVec)
          val newCtx = ctx.copy(env = env)
          getScalar(checkDataExpr(expr)(newCtx))(newCtx) match {
            case Payload(r: Record) if r.fields.length == 1 => r.fields.head.loType
            case other => other
          }
        }

        // Make sure the `init` expression has the right scalar type
        ctx.o.exprChildren map { expr =>
          val fields = input.subMask.fields
          val oldCtx: Context = ctx
          val t = {
            val newCtx: Context = oldCtx.copy(fields = fields)
            implicit val ctx = newCtx
            val initScalar: Scalar = getScalar(checkDataExpr(expr), Some(expr))
            checkSameType(newScalar, initScalar, expr)
          }
          t
        }

        val output = r match {
          case r: Reduce => {
            if (!input.hasVec) {
              error(s"Cannot apply Reduce to non-vector type $input")
            }
            def removeVec(d: Data): Data = d match {
              case v: Vec => v.subVec
              case a: Arr => a.copy(t = removeVec(a.t))
              case _ => d
            }
            removeVec(input.withoutChunks)
          }
          case nr: NestedReduce => {
            // A little hack to get around `.flatten`'s check against flattening
            // an array of scalars.
            var origVec = false
            val newSubArr = input.subArr match {
              case v: Vec => {origVec = true; v}
              case s: Scalar => Vec(s)
            }
            val out = getNested(input).withSubArr(newSubArr).flatten
            if (origVec)
              out
            else
              out.withSubArr(out.subVec)
          }
        }
        output.withSubVec(newScalar)
      }
      case b: Block => inputTypes.head
      case h: Hash64 => {
        val uint = h.bits match {
          case n if n <= 8 => lo.UInt8()
          case n if n <= 16 => lo.UInt16()
          case n if n <= 32 => lo.UInt32()
          case n if n <= 64 => lo.UInt64()
          case _ => error(s"More than 64 bits in hash")
        }
        val input = getContainer(inputTypes.head)
        input.withSubVec(Payload(uint))
      }
    }

    TypedHiResOp(ctx.o.ast, Func(fromTypes, toType), typedChildren.toList)
  }

  /** Returns all the fields in the given types */
  private def fieldGroups(types: Seq[Data])(implicit ctx: Context): Seq[Record.Group] = {
    val groupSeqs = for (t <- types.map(_.subVec.withMask(false))) yield {
      t match {
        case Payload(s: SplitRecord) => s.groups
        case Payload(f: FlatRecord) => Seq(Record.Group(f.fields:_*))
        case Payload(n: lo.NonRec) => Seq(Record.Group(Record.Field(n)))
        case Payload(f: lo.Record.Field) => Seq(Record.Group(f))
        case NamedPayload(name, nonRec) => Seq(Record.Group(Record.Field(nonRec, Some(lo.Id(name.name)))))
        case _ => {
          error(s"Attempting to Zip() non LoType.Primtive type $t")
        }
      }
    }
    groupSeqs.flatten
  }

  /** Returns the output structure for a parallel-input operator with given scalar `base` */
  private def broadcastResultType(base: Scalar, inputs: Seq[Data]): Data = {
    inputs.head.withSubVec(base)
  }

  private def checkSameType[T <: Data: Manifest](
      t1: T, t2: T, e: ExprListing)(implicit ctx: Context): T = {
    (t1, t2) match {
      case (HiResInt, Payload(i: lo.IntValued)) => t2
      case (HiResInt, NamedPayload(_, i: lo.IntValued)) => t2
      case (Payload(i: lo.IntValued), HiResInt) => t1
      case (NamedPayload(_, i: lo.IntValued), HiResInt) => t1
      case (Payload(p1), Payload(p2)) if p1.accepts(p2) => t1
      case (NamedPayload(_, p1), Payload(p2)) if p1.accepts(p2) => t1
      case (Payload(p1), NamedPayload(_, p2)) if p1.accepts(p2) => t1
      case (NamedPayload(_, p1), NamedPayload(_, p2)) if p1.accepts(p2) => t1
      case (_, _) if (t1 == t2) => t1
      case other => {
        error(s"Type $t1 appears in expression with incompatible type $t2", Some(e))
      }
    }
  }

  /** Returns the HiRes type of `e` occurring within [[Operator]] `o`
    *
    * @throws an exception if `e` fails type checking.
    */
  private def checkDataExpr(e: ExprListing)(implicit ctx: Context): Data = {
    def sameTypeExpr[T <: Data : Manifest](e1: ExprListing, e2: ExprListing, typeName: String): T = {
      val t1d = getType[T](checkDataExpr(e1), Some(e1), typeName)
      val t2d = getType[T](checkDataExpr(e2), Some(e2), typeName)
      checkSameType[T](t1d, t2d, e)
    }

    lazy val fieldNames: Map[String, lo.NonRec] = ctx.fields.map(f => f.name.map(_.name -> f.loType)).flatten.toMap
    e.ast match {
      case i: Id if fieldNames.contains(i.name) => Payload(fieldNames(i.name))
      case i: Id  => ctx.env.get(i) match {
        case Some(d: Data) => d
        case _ => error(s"Unknown symbol or field name $i", Some(e))
      }
			case Cast(_, t) => {
				checkDataExpr(e.children.head) match {
					case HiResInt => t
					case Payload(loType2)  => t
          case NamedPayload(name, loType2) => NamedPayload(name, t.loType.toNonRec)
					case other => error(s"Cannot convert $other to ${t.loType}")
				}
			}
      case Const(n) => HiResInt
      case FloatConst(f) => Payload(lo.LoFloat())
      case DoubleConst(d) => Payload(lo.LoDouble())
      case Length(o) => HiResInt
      case Plus(_, _) => sameTypeExpr[Scalar](e.children(0), e.children(1), "Scalar")
      case Div(_, _) => sameTypeExpr[Scalar](e.children(0), e.children(1), "Scalar")
      case Mul(_, _) => sameTypeExpr[Scalar](e.children(0), e.children(1), "Scalar")
      case Pow(_, _) => sameTypeExpr[Scalar](e.children(0), e.children(1), "Scalar")
      case Pow2(e1) => getScalar(checkDataExpr(e.children.head)) 
      case Log2Up(_) => getScalar(checkDataExpr(e.children.head))
      case Neg(_) => getScalar(checkDataExpr(e.children.head))
      case True => lo.Bool()
      case False => lo.Bool()
      case Less(_, _) =>  { sameTypeExpr[Scalar](e.children(0), e.children(1), "Scalar"); lo.Bool() }
      case Greater(_, _) =>  { sameTypeExpr[Scalar](e.children(0), e.children(1), "Scalar"); lo.Bool() }
      case LessEq(_, _) =>  { sameTypeExpr[Scalar](e.children(0), e.children(1), "Scalar"); lo.Bool() }
      case GreaterEq(_, _) =>  { sameTypeExpr[Scalar](e.children(0), e.children(1), "Scalar"); lo.Bool() }
      case Equal(_, _) =>  { sameTypeExpr[Scalar](e.children(0), e.children(1), "Scalar"); lo.Bool() }
      case Not(_) =>  { getBool(checkDataExpr(e.children.head)) }
      case And(_, _) => { getBool(checkDataExpr(e.children(0))); getBool(checkDataExpr(e.children(1))); lo.Bool() }
      case Or(_, _) => { getBool(checkDataExpr(e.children(0))); getBool(checkDataExpr(e.children(1))); lo.Bool() }
      case c: CommutativeOpExpr => sameTypeExpr[Scalar](e.children(0), e.children(1), "Scalar")
      case b: BitRange => {
        val word = getPayload(checkDataExpr(e.children(0))).loType.toIntValued
        getHiResInt(checkDataExpr(e.children(1)))
        getHiResInt(checkDataExpr(e.children(2)))
        Payload(word)
      }
      case UField(field) => {
        if (field >= ctx.fields.length) {
          error(s"Attempting to extract field $field from record with fields ${ctx.fields}")
        }
        Payload(ctx.fields(field).loType)
      }
    }
  }

  /** Checks the type of a hash function's record input and errors if not an unsigned integer */
  private def checkHash(rec: Primitive)(implicit ctx: Context): Unit = rec match {
    case Payload(i: lo.IntValued) if i.signed==false =>
    case NamedPayload(_, i: lo.IntValued) if i.signed==false =>
    case t => error(s"Non (unsigned) int-valued type $t used as hash function")
  }

  /** Throws an exception for a failed type-check
    *
    * @param prefix the context-specific error message to precede expression/op metadata
    * @param e an optional expression in which the error occurs
    */
  private def error[T](
      prefix: String,
      e: Option[ExprListing]=None)
    (implicit ctx: Context): T = {

    val childLen = 80
    val (startLine, endLine) = e match {
      case Some(list) => (list.lines.head.num, list.lines.last.num)
      case None => (ctx.o.lines.head.num, ctx.o.lines.last.num)
    }
    val estr = e.map(e => { val l = new Line(""); e.ast.addToLine(l); l.string})
    throw new Error(
      "\n\n" + "-"*90 + "\n" +
      prefix +
      (if (e.nonEmpty) s"\n  In expression ${estr.get}\n" else "" )+
      s"  In operator: ${ctx.o.ast.abbreviated(childLen)}\n" +
      s"  On lines ${startLine} to ${endLine}\n" +
      s"  With external environment:" +
      (this.externalEnv.foldLeft("")) { case (s, (id, t)) => s"$s\n    $id -> $t" } +
      s"\n  And fields:\n" +
      ctx.fields.map(f => s"    $f").mkString("\n") +
      "\n" + "-"*90 + "\n\n")
  }

  /** Returns HiType `t` as an element of type `T` or throws an error
    *
    * @tparam T the type to which `t` should be coerced, if possible
    * @param t the `HiType` to be checked for adherence to type-class `T`
    * @param e optional expression in which the type `t` occurs
    * @param typeName a string representation of `T` for use in a possible error message
    */
  private def getType[T <: Data : Manifest](
      t: HiType,
      e: Option[ExprListing],
      typeName: String)(implicit ctx: Context): T = {
    t match {
      case t2: Data if t2.masked => getType[T](t2.withMask(false), e, typeName)
      case t2: T => t2
      case _ => {
        val prefix = 
          s"Operator type check error:\n" +
          s"  Expected type $typeName where $t encountered\n"
        error(prefix, e)
     }
   }
 }

 private def getContainer(t: HiType, e: Option[ExprListing]=None)(implicit ctx: Context) = getType[Container](t, e, "Container")
 private def getArr(t: HiType, e: Option[ExprListing]=None)(implicit ctx: Context) = getType[Arr](t, e, "Arr")
 private def getNested(t: HiType, e: Option[ExprListing]=None)(implicit ctx: Context) = getType[NestedData](t, e, "NestedData")
 private def getVec(t: HiType, e: Option[ExprListing]=None)(implicit ctx: Context) = getType[Vec](t, e, "Vec")
 private def getScalar(t: HiType, e: Option[ExprListing]=None)(implicit ctx: Context) = getType[Scalar](t, e, "Scalar")
 private def getBool(t: HiType, e: Option[ExprListing]=None)(implicit ctx: Context) = {
   val s = getScalar(t)
   s match {
     case p @ Payload(lo.Bool(_)) => p
     case p @ NamedPayload(_, lo.Bool(_)) => p
     case _ => error(s"$s found where boolean expected", e)
   }
 }
 private def getHiResInt(t: HiType, e: Option[ExprListing]=None)(implicit ctx: Context) = getType[HiResInt.type](t, e, "HiResInt")
 private def getHistogram(t: HiType, e: Option[ExprListing]=None)(implicit ctx: Context): Hist = t match {
   case a: Arr if a.histogram.nonEmpty => getHistogram(a.histogram.get)
   case a: Arr => getHistogram(a.t, e)
   case h: Hist => h
   case _ => error(s"No histogram found in type for expression $e")
 }
 private def getPayload(t: HiType, e: Option[ExprListing]=None)(implicit ctx: Context) = getType[PayloadLike](t, e, "Payload")
 private def getRecord(t: HiType, e: Option[ExprListing]=None)(implicit ctx: Context) = {
   val pay = getPayload(t, e)
   pay match {
     case Payload(r: Record) => r
     case NamedPayload(r: Record, _) => r
     case other => {
       error(s" Expected Record type where type $other encountered\n", e)
     }
   }
 }
}

