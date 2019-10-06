// See LICENSE.txt
package ressort.hi.compiler
import ressort.compiler.CompilerConfig
import ressort.hi._
import ressort.lo
import scala.collection.mutable.HashMap

/** Generates an appropriate [[MetaArray]] type for the output of a given
  * [[Operator]] and its [[MetaArray]] inputs.
  */
class OutputArrayGenerator(funcType: Func, config: CompilerConfig) {
  /** Returns a [[MetaArray]] appropriate for the output of `op`, and a list of any new buffers allocated  for it */
  def apply(op: TypedHiResOp, inputs: List[MetaArray], nodeId: Option[Integer]): (MetaArray, List[Buffer]) = {
    val (outputArray, newBuffers) = inner(op, inputs, nodeId)
    if (outputArray.isInstanceOf[MultiArray]) {
      return (outputArray, newBuffers)
    }

    (outputArray, newBuffers)
  }

  private def makeMask(array: MetaArray): Buffer = {
    new Buffer(
      name = MetaArray.tempIds.newId("mask"),
      recType = lo.Bool(),
      length = array.cloneBufferLength,
      numValid = array.buffer.numValid)
  }

  /** Name or base of name to use for buffers created by `op` */
  private def name(op: TypedHiResOp, suffix: String=""): lo.SymLike = {
    val base = op.funcType.to.subMask match {
      case n: NamedPayload => n.name.name
      case _ => "t"
    }
    val res = MetaArray.tempIds.newId(s"${base}_${suffix}")
    res
  }

  private def inner(
      op: TypedHiResOp,
      inputs: List[MetaArray],
      nodeId: Option[Integer]): (MetaArray, List[Buffer]) = op.o match {
    case o: IdOp => {
      var immaterial = false
      var scalar = false
      val recType = {
        val hiType = op.funcType.from(o.id)
        val arrScalarType = hiType match {
          case c: Container => c.subVec
          case s: Scalar => {
            immaterial = true
            scalar = true
            s
          }
          case _ => throw new Error("HiRes input has unknown type $hiType")
        }
        arrScalarType
      }
      val buf =
        new Buffer(
          lo.Expr(o.id).asInstanceOf[lo.SymLike],
          lo.LoType(recType).toPrimitive,
          (if (scalar) lo.Const(1) else lo.Expr(Length(o))),
          allocate = false, immaterial = immaterial, scalar = scalar)
      (FlatArray(buf, None), List(buf))
    }

    case o: InsertionSort => {
      val input = inputs.head
      input.clone(name(op, "isrt"))
    }
    
    case o: SplitPar => {
      val input = inputs.head
      val arr = {
        o.slices match {
          case Const(0) => EmptyShellArray(input.cloneRef())
          case _ => 
            SlicedArray(
              base              = input.cloneRef(),
              slices            = lo.Expr(o.slices),
              parallel          = true,
              cloneDisjoint     = o.disjoint,
              padding           = lo.Const(0),
              paddingToAdd      = lo.Expr(o.padding))
        }
      }
      (arr, Nil)
    }

    case o: SplitSeq => {
      val input = inputs.head
      val arr = {
        o.slices match {
          case Const(0) => EmptyShellArray(input.cloneRef())
          case _ =>
            SlicedArray(
              base              = input.cloneRef(),
              slices            = lo.Expr(o.slices),
              parallel          = false,
              cloneDisjoint     = o.disjoint,
              padding           = lo.Const(0),
              paddingToAdd      = lo.Expr(o.padding))
        }
      }
      (arr, Nil)
    }

    case o: Histogram => {
      val recs = inputs(0)
      val hist = histogramArray(recs, lo.Expr(o.slices), lo.Expr(o.padding))
      hist.buffer.name = name(op, "hist")
      (hist, hist.buffers.toList)
    }

    case o: Collect => {
      val arrInput = inputs(0)
      val (newBase, baseAllocs) = {
        // Eventually, when `padding` is added to `Collect`, we will use this
        // to calculate a new buffer size.
        val name = this.name(op, "coll")
        val (arr, allocs) = arrInput match {
          case n: NestedArray => n.base.clone(name)
          case other => other.clone(name)
        }
        (arr.withMask(None), allocs)
      }

      // Allocate a "slice length histogram" if this a nested collect and none yet exists
      var newHist = false
      val (arr, sliceLengths, numValidAllocs) = arrInput match {
        case n: NestedArray => {
          newHist = n.numValid.isEmpty
          var allocs = Set[Buffer]()
          val numValid =
            n.numValid.map(_.cloneRef()) getOrElse makeSliceLengths(n)
          if (newHist) {
            numValid.buffer.name = name(op, "slen")
            numValid.buffers.map(_.mustMaterialize = true)
            allocs ++= numValid.buffers
          }
          val arr = n.withBase(newBase)
            .asNestedArray.get
            .withSliceLengths(Some(numValid))
          (arr, Some(numValid), allocs)
        }
        case other => (newBase, None, Set[Buffer]())
      }

      // If this is a flat array collect, introduce a numValid counter that will be
      // propagated acorss successive arrays derived from this one
      arr match {
        case f: FlatArray => {
          val nval = name(op, "nval")
          arr.buffer.numValid = Some(nval)
        }
        case _ =>
      }

      (arr, numValidAllocs.toList ++ baseAllocs)
    }
        
    case o: Offsets => {
      val input = inputs.head
      val res = input match {
        case _ if o.disjoint => {
          // For disjoint partitioning, also return a separate histogram of total
          // partition sizes, and combine them in a multi-array
          val (offs, offAllocs) = input.clone(name(op, "off"))
          val (sizes, sizeAllocs) = if (o.depth > 0) {
            val base = offs.asNestedArray.get.base match {
              case d: DisjointBase => FlatArray(d.buffer)
              case o => o
            }
            base.clone(name(op, "size"), length = offs.buffer.length / offs.length)
          } else {
            offs.clone(name(op, "size"))
          }
          val arr = MultiArray(offs, sizes)
          (arr, offAllocs ++ sizeAllocs)
        }
        case n: NestedArray if !o.inPlace => {
          val arr = histogramArray(n.base, slices = n.length)
          arr.buffer.name = name(op, "off")
          (arr, arr.buffers.toList)
        }
        case _ => input.clone(name(op, "off"))
      }
      res
    }

    case o: LastArray => {
      inputs.head match {
        case m: MultiArray => m.tail.last.clone(name = name(op, "mrgd"), length = m.tail.last.buffer.length)
        case _ => {
          val input = inputs.head.asNestedArray.get
          val bufLen = (input.buffer.length - (input.padding * input.length)) / input.length
          input
          .withPadding(lo.Const(0))
          .cloneContiguous._1
          .flatten
          .clone(name(op, "mrgd"), length = bufLen)
        }
      }
    }

    case o: RestoreHistogram => {
      val values = inputs.head
      val hist = inputs.tail.head
      val arr = values match {
        case d: DisjointArray => {
          DisjointSlice(
            base = d.cloneRef(),
            slices = hist.maxWindowSize-lo.Const(1),
            numValid = Some(hist.cloneRef()))
        }
        case _ => HistSlicedArray(base = values.cloneRef(), hist = hist.cloneRef())
      }
      (arr, Nil)
    }

    case o: Partition => {
      val keyInput = inputs(0)
      val arrInput = inputs(1)
      val histInput = inputs(2)

      // In the case of a disjoint partition, the "histogram" will actually be a
      // multi-array containing both the histogram and a "size" array.
      // For allocation right now, we only need the former.
      val offs = histInput match {
        case m: MultiArray => (m.head)
        case _ if !o.disjoint => histInput
        case _ =>
          throw new Error(
            s"Expected MultiArray for parallel disjoint offsets, but found:\n" +
            s"${histInput.mkString(0)}")
      }

      val (base, allocs) = {
        val nelems = {
          val prevPadding = arrInput match {
            case n: NestedArray => n.padding
            case _ => lo.Const(0)
          }
          arrInput.cloneBufferLength - (prevPadding * arrInput.length)
        }
        val newName = name(op, "part")
        val (arr, allocs) = if (o.disjoint) { 
          val in = if (o.parallel) {
            val length = offs.buffer.length / offs.length
            val base = offs.clone(newName, recType = arrInput.recType, length = length)._1
            val res = base.asNestedArray.get.base
            SlicedArray(res, slices = res.maxWindowSize-lo.Const(1), parallel=true)
          } else {
            val base = arrInput.clone(newName, recType = arrInput.recType)._1
            SlicedArray(base, slices = offs.maxWindowSize-lo.Const(1), parallel=true)
          }
          val res = DisjointArray.cloneFrom(in, newName, initPointersNull=true)
          res
        } else {
          val (init, allocs) = arrInput.clone(newName, length = nelems)
          if (o.parallel)
            (init.asNestedArray.get.base, allocs)
          else
            (init, allocs)
        }

        val out = if (o.disjoint) {
          arr.asNestedArray.get.base
        } else {
          arr
        }
        (out.withMask(None), allocs)
      }


      // Software write-combining buffer to hold one cache line of records for each
      // partition, and a local mini-histogram to count how full each buffer slot is
      val (swwcb, miniHist) = {
        val recType = arrInput.buffer.recType
        val partBufLen = PartitionGenerator.swwcbLength(config.rpart.linesz, recType)
        val parts = (offs.buffer.length / offs.deepNumSlices) - lo.Const(1)
        val bufLen = parts * partBufLen
        val swwcb = inputs.head.ancillary(recType, bufLen, name(op, "swwcb"))
        val hist = inputs.head.ancillary(lo.UInt8(), parts, name(op, "swwcb_hist"))
        hist.buffer.initializer = Some(lv => lo.Assign(lv, lo.Const(0)))
        (swwcb, hist)
      }


      val arr =
        MultiArray(
          base,
          offs.cloneRef(), 
          swwcb,
          miniHist)
      base.buffer.numValid = None
      (arr, (swwcb.buffers ++ miniHist.buffers).toList ++ allocs)
    }

    case o: HashTable => {
      val recInput = inputs.head
      val hashInput = o.hash.map(_ => inputs.tail.head)
      val keyBits = HashTableGenerator.keyWidthBits(o, recInput.recType)
      val buckets: lo.Expr = (o.buckets, hashInput) match {
        case (Some(b), _) => lo.Expr(b)
        case (_, Some(h)) => lo.Expr(Const(1 << h.recType.toFixedWidthInt.maxBytes))
        case _ if keyBits <= 16 => lo.Expr(Const(1 << keyBits))
        case _ => lo.Pow2(lo.Log2Up(recInput.cloneBufferLength - lo.Const(1)))
      }
      // TODO: add widths to HiRes types so we can do this properly and set slots t allocate
      // at least a cache line per bucket
      val slots: lo.Expr = lo.Expr(o.slots.getOrElse({ println(s"WARNING: CHOSE SLOTS=4"); Const(4) }))
      chunkArray(
          op,
          base = recInput,
          buckets = buckets,
          slots = slots,
          onePerSlice=true,
          inlineCounter=o.inlineCounter)
    }

    case o: HashJoin => {
      val left = inputs(0)
      val right = inputs(1)
      val hash = inputs(2)
      // HashJoin is special in that it only adds nesting if none was present, so adjust
      val (base, buckets) = left match {
        case f: FlatArray => (f, lo.Const(1))
        case n: NestedArray => (n.base, n.length)
      }
      // The default number of slots assumes that the left relation's tuples match
      // one record each in the hash table.  A future version of this operator should
      // make this a parameter.
      val slots = left.buffer.length / buckets
      chunkArray(op, base = base, buckets = buckets, slots = slots, onePerSlice=false, inlineCounter = false)
    }

    case o: Flatten => {
      val struct = inputs.head
      (struct.asNestedArray.get.base.cloneRef(), Nil)
    }

    case o: Compact => {
      val old = inputs.head.asNestedArray.get
      val lenVar = name(op, "len")
      val (nelems, dynamicSize) = (o.hist, inputs.head) match {
        case (Some(h), _) =>  (lenVar, true) // Mark dynamic allocation
        case (_, _) =>
          // Don't try to factor out old.numElements, because using unsigned arithmetic
          val len =
            old.cloneBufferLength -
              (old.padding * old.length) +
              (lo.Expr(o.padding) * old.length)
          (len, false)
      }
      val (clone, allocs) = inputs.head.clone(name(op, "cpct"), length = nelems)
      var res = o.hist match {
        case Some(h) => {
          val hist = inputs(1)
          def convert(a: MetaArray): MetaArray = a match {
            case n: NestedArray => {
              val base = convert(n.base)
              // TODO: this should eventually be a [[HistSliceArray]] but will require
              // necessary code to set proper histogram entries (& allocate them).
              EmptyShellArray(base)
            }
            case d: DisjointBase => {
              // Special case required to handle conversion of disjoint to contiguous:
              // (this only happens in [[Compact]] and [[Partition]]
              d.buffer.allocate = true // Disjoint buffers aren't allocated; so reset
              FlatArray(d.buffer, d.mask)
            }
            case f: FlatArray => f
          }
          val base = convert(clone.asNestedArray.get.base)
          HistSlicedArray(
            base = base,
            hist = hist.cloneRef())
        }
        case None => clone.withPadding(lo.Expr(o.padding))
      }
      res = res.withMask(None)
      res.buffer.dynamicSize = dynamicSize
      (res, allocs)
    }

    case o: Eval => {
      val recType = lo.LoType(op.funcType.to.subMask).toPrimitive
      inputs.head.clone(name(op), recType = recType)
    }

    case o: Position => {
      inputs.head.clone(name(op, "pos"), recType = lo.Index())
    }

    case o: Hash64 => {
      inputs.head.clone(name(op, "h64"), recType = lo.UInt64())
    }

    case o: Block => (inputs.head.cloneRef(), Nil)

    case o: Reduce => {
      val old = inputs.head
      val recType = old.recType
      var (arr, allocs) = inputs.head.cloneFixedLengthSlices(name(op, "red"), recType, old.deepNumSlices)
      arr.buffer.scalar = true
      if (o.init.isEmpty)
        arr = arr.withMask(Some(makeMask(arr)))
      else
        arr = arr.withMask(None)
      (arr, allocs)
    }

    case o: NestedReduce => {
      val old = inputs.head.asNestedArray.get
      val recType = old.recType
      var (arr, allocs) =
        old
          .withPadding(lo.Const(0))
          .cloneContiguous._1
          .cloneFixedLengthSlices(
            name(op, "nred"),
            recType,
            (old.maxWindowSize - old.padding) * old.flatten.deepNumSlices)
      arr.buffer.scalar = !op.funcType.to.hasVec
      arr = arr.flatten
      if (o.init.isEmpty)
        arr = arr.withMask(Some(makeMask(arr)))
      else
        arr = arr.withMask(None)
      (arr, allocs)
    }

    case o: Zip => {
      val recType = {
        val hiType = op.funcType.to
        lo.LoType(hiType.subMask).toPrimitive
      }
      var (arr, allocs) = inputs.head.clone(name(op, "zip"), recType = recType)
      arr.buffer.scalar = !op.funcType.to.hasVec
      (arr, allocs)
    }

    case o: Project => {
      val recType = {
        val hiType = op.funcType.to
        lo.LoType(hiType.subMask).toPrimitive
      }
      var (arr, allocs) = inputs.head.clone(name(op, "prj"), recType = recType)
      arr.buffer.scalar = !op.funcType.to.hasVec
      (arr, allocs)
    }

    case o: Mask => {
      val base = inputs.head
      val mask = makeMask(base)
      mask.name = name(op, "mask")
      var arr = inputs.head.cloneRef()
      arr = arr.withMask(Some(mask))
      (arr, mask :: Nil)
    }

    case o: Gather => {
      val index = inputs(0)
      val target = inputs(1)
      inputs.head.clone(name(op, "gth"), recType = target.buffer.recType)
    }

    case o: Cat => {
      val inputArrays = inputs.map(_.cloneRef())
      (MultiArray(inputArrays.head, inputArrays.tail:_*), Nil)
    }

    case o: Uncat => {
      val input = inputs.head.asInstanceOf[MultiArray]
      val arr = if (o.n > 0) input.tail(o.n-1) else input.head
      (arr, Nil)
    }

    case DagOp(_) => {
      (inputs.head.cloneRef(), Nil)
    }
  }


  /** Returns a new [[MetaArray]] containing the histogram used when
    * partitioning `base`
    */
  def histogramArray(
      base:             MetaArray,
      slices:           lo.Expr,
      padding: lo.Expr = lo.Const(0)): MetaArray = {
    def ancillary(base: MetaArray): MetaArray = {
      val numElements = slices  + lo.Const(1) + padding
      val recType = lo.Index()
      val name = MetaArray.tempIds.newId("hist")
      val res = base.ancillary(recType, numElements, name)
      res.buffer.mustMaterialize = true
      res.buffer.initializer = Some(lv => lo.Assign(lv, lo.Const(0)))
      res
    }
    ancillary(base)
  }

  /** Returns a [[ChunkArray]] with record type an structure derived from `base`, and allocations */
  def chunkArray(
      op: TypedHiResOp,
      base: MetaArray,
      buckets: lo.Expr,
      slots: lo.Expr,
      onePerSlice: Boolean,
      inlineCounter: Boolean): (ChunkArray, List[Buffer]) = {
    val loRec = lo.LoType(op.funcType.to.subMask).toPrimitive
    val bucketRec = ChunkArray.bucketRec(loRec, base.mask.nonEmpty)
    val (newBase, baseAllocs) = {
      val dummy = if (inlineCounter) lo.Const(1) else lo.Const(0)
      val len = buckets * (slots + dummy) * (if (onePerSlice) base.deepNumSlices else lo.Const(1))
      base.cloneFixedLengthSlices(name(op, "chks"), recType = loRec, length = len)
    }
    val countsName = name(op, "cts")
    val ptrsName = name(op, "ptrs")
    var arr =
    ChunkArray(
      newBase,
      counts = newBase.ancillary(lo.Index(), buckets, countsName),
      pointers =
      newBase.ancillary(bucketRec, buckets, ptrsName),
      buckets = buckets,
      slots = slots,
      inlineCounter = inlineCounter)
    arr.pointers.buffer.initializer = Some(arr.initPointerStruct)
    arr.pointers.buffer.finalizer = Some(arr.freePointerStruct)
    arr.counts.buffer.initializer = Some(lv => lo.Assign(lv, lo.Const(0)))
    arr.buffer.initializer = Some(arr.initDummyCounter)
    arr = arr.withMask(None)
    val allocs = (arr.counts.buffers.toList ++ arr.pointers.buffers.toList ++ baseAllocs).reverse
    (arr, allocs)
  }

  private def makeSliceLengths(n: NestedArray): MetaArray = {
    val recType = lo.Index()
    val name = MetaArray.tempIds.newId("slen")
    SlicedArray(
      base = n.base.ancillary(recType, n.length, name), // Will result in one per slice
      slices = n.length,
      parallel = true)
  }


  /** Returns a new [[MetaArray]] that can contain the result of merging
    * the previously independent histograms in histogram-partitioned array
    * structure `hpin`.
    */
  def mergeHistogramStructures(hpin: HistSlicedArray) = {
    val oldHist = hpin.hist

    // The reduction removes a level of structure from the histogram,
    // so we must assume it's a nested array.
    val histNest = oldHist.asNestedArray.get
    val histInner = histNest.base
    
    // Make a new buffer structure for the histogram
    // Note: divisor cannot just be `hpin.numElements` because the
    // histogram is padded with at least one element per slice
    val hist = hpin.hist
    val numElements = histNest.buffer.length / hist.length
    val name = MetaArray.tempIds.newId("hist")
    histInner.clone(name, length = numElements)
  }


}
