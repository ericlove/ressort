// See LICENSE.txt
package ressort.example
import ressort.hi._
import ressort.lo
import ressort.lo.interp._


object TpchSchema {

  def makeField(name: Symbol, loType: lo.NonRec) = {
    lo.Record.Group(lo.Record.Field(name = Some(name), loType = loType))
  }

  val lineitem = Vec(lo.SplitRecord(name = Some('lineitem), groups = Seq(
    makeField('l_extendedprice,  lo.LoFloat()),
    makeField('l_discount,       lo.LoFloat()),
    makeField('l_tax,            lo.LoFloat()),
    makeField('l_partkey,        lo.UInt32()),
    makeField('l_quantity,       lo.UInt32()),
    makeField('l_shipmode,       lo.UInt8()),
    makeField('l_shipinstruct,   lo.UInt8()),
    makeField('l_shipdate,       lo.UInt16()),
    makeField('l_receiptdate,    lo.UInt16()),
    makeField('l_commitdate,     lo.UInt16()),
    makeField('l_returnflag,     lo.UInt8()),
    makeField('l_linestatus,     lo.UInt8()))))

  val part = Vec(lo.SplitRecord(name = Some('part), groups = Seq(
    makeField('p_partkey, lo.UInt32()),
    makeField('p_container, lo.UInt8()),
    makeField('p_brand, lo.UInt8()),
    makeField('p_size, lo.UInt8()),
    makeField('p_type, lo.UInt8()),
    makeField('p_retailprice, lo.LoFloat())
  )))

  val order = Vec(lo.SplitRecord(name = Some('order), groups = Seq(
    makeField('o_orderkey, lo.UInt32()),
    makeField('o_custkey, lo.UInt32()),
    makeField('o_orderstatus, lo.UInt8()),
    makeField('o_totalprice, lo.LoFloat()),
    makeField('o_orderdate, lo.UInt32()),
    makeField('o_orderpriority, lo.UInt8()),
    makeField('o_shippriority, lo.UInt8()),
    makeField('o_clerk, lo.UInt32())
  )))

  val STARTDATE = Const(0)
  val CURRENTDATE = Const(366 * 5 + 31 * 6 + 17)
  val ENDDATE = Const(366 * 7)

  /** l_shipmode values */
  val AIR  = Const(1)
  val AIR_REG  = Const(2)

  /** l_shipinstruct values */
  val DELIVER_IN_PERSON  = Const(1)

  /** p_brand values */
  val BRAND12  = Const(12)
  val BRAND23  = Const(23)
  val BRAND34  = Const(34)

  /** p_container values */
  val SM_CASE    = Const(0)
  val SM_BOX     = Const(1)
  val SM_PACK    = Const(2)
  val SM_PKG     = Const(3)
  val MED_BAG    = Const(4)
  val MED_BOX    = Const(5)
  val MED_PKG    = Const(6)
  val MED_PACK   = Const(7)
  val LG_CASE    = Const(9)
  val LG_BOX     = Const(10)
  val LG_PACK    = Const(11)
  val LG_PKG     = Const(12)

  object PartTypes {
    /** p_part TYPE Syllable 1 Values */
    val STANDARD = Const(0)
    val SMALL = Const(1)
    val MEDIUM = Const(2)
    val LARGE = Const(3)
    val ECONOMY = Const(4)
    val PROMO = Const(5)
    val TypesSyllable1 = List(STANDARD, SMALL, MEDIUM, LARGE, ECONOMY, PROMO)

    /** p_part TYPE Syllable 2 Values */
    val ANODIZED = Const(0)
    val BURNISHED = Const(1)
    val PLATED = Const(2)
    val POLISHED = Const(3)
    val BRUSHED = Const(4)
    val TypesSyllable2 = List(ANODIZED, BURNISHED, PLATED, POLISHED, BRUSHED)

    /** p_part TYPE Syllable 3 Values */
    val TIN = Const(0)
    val NICKEL = Const(1)
    val BRASS = Const(2)
    val STEEL = Const(3)
    val COPPER = Const(4)
    val TypesSyllable3 = List(TIN, NICKEL, BRASS, STEEL, COPPER)
  }

  /** Line and order status */
  val N = Const(1)
  val O = Const(2)
  val R = Const(3)
  val A = Const(4)
  val F = Const(5)
  val P = Const(6)

  /** Priorities */
  val URGENT = Const(1)
  val HIGH = Const(2)
  val MEDIUM = Const(3)
  val NOT_SPECIFIED = Const(4)
  val LOW = Const(5)

  class Generator(scale: Float) {
    import ressort.lo._


    val partSize = (scale * 2.0e5).toInt
    val orderSize = (scale * 1.5e6).toInt
    val custSize = (scale * 1.5e5).toInt


    val p_partkey   = new Array[Int](partSize)
    val p_brand     = new Array[Int](partSize)
    val p_container = new Array[Int](partSize)
    val p_size      = new Array[Int](partSize)
    val p_type      = new Array[Int](partSize)
    val p_retailprice = new Array[Float](partSize)


    val o_orderkey = new Array[Int](orderSize)
    val o_custkey = new Array[Int](orderSize)
    val o_orderstatus = new Array[Int](orderSize)
    val o_totalprice = new Array[Float](orderSize)
    val o_orderdate = new Array[Int](orderSize)
    val o_orderpriority = new Array[Int](orderSize)
    val o_clerk = new Array[Long](orderSize)
    val o_shippriority = new Array[Int](orderSize)
    val o_num_litems = new Array[Int](orderSize)

    var o_key = 0
    for (i <- (0 until orderSize)) {
      o_custkey(i) = (math.random * (custSize-1.0)).toInt
      // Customer key must not be divisible by three, per TPC-H spec
      if (o_custkey(i) % 3 == 0)
        o_custkey(i) +=  (if (math.random > 0.5) 1 else 2)
      o_num_litems(i) = (math.random * 7.0 + 1.0).toInt

      // In order to generate a sparse orderkey, use only the first 8 of every 32 indices
      o_orderkey(i) = o_key
      o_key += 1
      o_key += (if (o_key % 8 == 0) 24 else 0)

      o_orderdate(i) = STARTDATE.n + (math.random * (ENDDATE.n - 151 - STARTDATE.n + 1)).toInt + 1
      o_orderpriority(i) = (math.random * 5.0).toInt + 1
      o_shippriority(i) = 0
      o_clerk(i) = (math.random * (scale * 1000 + 1.0)).toInt + 1

      // Rest of orders table depends on the lineitem table, which depends on this
    }

    val litemSize = o_num_litems.sum

    val l_orderkey      = new Array[Int](litemSize)
    val l_partkey       = new Array[Int](litemSize)
    val l_suppkey       = new Array[Int](litemSize)
    val l_linenumber    = new Array[Int](litemSize)
    val l_quantity      = new Array[Int](litemSize)
    val l_extendedprice = new Array[Float](litemSize)
    val l_discount      = new Array[Float](litemSize)
    val l_tax           = new Array[Float](litemSize)
    val l_returnflag    = new Array[Int](litemSize)
    val l_linestatus    = new Array[Int](litemSize)
    val l_shipdate      = new Array[Int](litemSize)
    val l_commitdate    = new Array[Int](litemSize)
    val l_receiptdate   = new Array[Int](litemSize)
    val l_shipinstruct  = new Array[Int](litemSize)
    val l_shipmode      = new Array[Int](litemSize)

    val orderData = Map(
      'o_orderkey -> o_orderkey,
      'o_custkey -> o_custkey,
      'o_orderstatus -> o_orderstatus,
      'o_totalprice -> o_totalprice,
      'o_orderdate -> o_orderdate,
      'o_orderpriority -> o_orderpriority,
      'o_clerk -> o_clerk,
      'o_shippriority -> o_shippriority
    )

    for (i <- (0 until partSize)) {
      p_partkey(i)    = i
      p_brand(i)      = (math.random * 24.0).toInt
      p_container(i)  = (math.random * 39.0).toInt
      p_size(i)       = (math.random * 49.0).toInt + 1
      p_type(i)       = (math.random * 150.0).toInt
      p_retailprice(i)= (90000 + ((i/10) % 20001) + 100 * (i % 1000))
    }

    val partData = Map(
      'p_partkey    -> p_partkey,
      'p_brand      -> p_brand,
      'p_container  -> p_container,
      'p_size       -> p_size,
      'p_type       -> p_type,
      'p_retailprice -> p_retailprice
    )

    // Can finally compute lineitem table now that size / rows per order are known
    {
      var i = 0
      val S = (scale * 10000).toInt
      for (j <- (0 until orderSize)) {
        val rows = o_num_litems(j)
        var allF = true
        var allO = true
        var totalprice = 0.0
        for (k <- (0 until rows)) {
          l_orderkey(i)       = o_orderkey(j)
          l_partkey(i)        = (math.random * partSize       ).toInt
          val pkey = l_partkey(i)
          l_suppkey(i)        = (pkey + ((math.random * 4.0).toInt * (S/4 + (pkey-1)/S))) % S + 1
          l_linenumber(i)     = k
          l_quantity(i)       = (math.random * 51.0           ).toInt
          l_extendedprice(i)  = l_quantity(i) * p_retailprice(pkey)
          l_discount(i)       = (math.random * 101.0).toInt.toFloat / 1000.0.toFloat
          l_tax(i)            = (math.random * 81.0).toInt.toFloat / 1000.0.toFloat
          l_returnflag(i)     = (if (l_shipdate(i) > CURRENTDATE.n) N.n else if (math.random > 0.5) R.n else A.n)
          l_linestatus(i)     = (if (l_shipdate(i) > CURRENTDATE.n) O.n else F.n)
          l_shipdate(i)       = o_orderdate(j) + (math.random * 121.0).toInt + 1
          l_commitdate(i)     = o_orderdate(j) + (math.random * 91.0).toInt + 30
          l_receiptdate(i)    = l_shipdate(i) + (math.random * 31.0).toInt
          l_shipinstruct(i)   = (math.random * 6.0            ).toInt
          l_shipmode(i)       = (math.random * 3.0            ).toInt

          allF &&= (l_linestatus(i) == F.n)
          allO &&= (l_linestatus(i) == O.n)
          totalprice += l_extendedprice(i) * (1.0 + l_tax(i)) * (1.0 - l_discount(i))
          i += 1
        }
        o_orderstatus(j) = if (allF) F.n else if (allO) O.n else P.n
        o_totalprice(j) = totalprice.toFloat
      }
    }

    val litemData = Map[Symbol, Array[_]](
      'l_extendedprice  -> l_extendedprice ,
      'l_discount       -> l_discount      ,
      'l_tax            -> l_tax           ,
      'l_partkey        -> l_partkey       ,
      'l_quantity       -> l_quantity      ,
      'l_shipmode       -> l_shipmode      ,
      'l_shipinstruct   -> l_shipinstruct  ,
      'l_shipdate       -> l_shipdate      ,
      'l_receiptdate    -> l_receiptdate   ,
      'l_commitdate     -> l_commitdate    ,
      'l_returnflag     -> l_returnflag    ,
      'l_linestatus     -> l_linestatus
    )

    /** Returns the `index`th element of `data` as an [[EVal]] of appropriate type */
    def readArray[T](index: EVal, loType: NonRec, data: Array[T]): EVal = {
      def toEVal(d: T): EVal = d match {
        case d: Double => EDouble(d)
        case f: Float => EFloat(f)
        case i: Int => loType match {
          case iv: IntValued => EInt(i.toLong, iv.minBytes, iv.signed)
          case _ => ???
        }
        case l: Long => loType match {
          case iv: IntValued => EInt(l.toLong, iv.minBytes, iv.signed)
          case _ => ???
        }
        case _ => ???
      }
      val n = index.toEInt(None).i
      toEVal(data(n.toInt))
    }

    def allocateRelation(relation: lo.Record, data: Map[Symbol, Array[_]]): LoAst = {
      val symbol = Symbol(relation.name.get.name)
      val types = relation.fields.map(f => Symbol(f.name.get.name) -> f.loType).toMap
      val length = data(data.keys.head).size
      Dec(symbol, Ptr(Arr(relation))) +
      HeapAlloc((symbol), Some(length)) +
      ForBlock('i, length,
        Block(data.keys.toList.map { k =>
          (Deref(symbol).sub('i).dot(k)
              :=
              Escape(
                'i,
                Index(),
                types(k),
                n => readArray(n, types(k), data(k))))
        }))
    }

    def allocate: LoAst = {
      allocateRelation(lineitem.subVec.asInstanceOf[Payload].loType.asInstanceOf[lo.Record], litemData) +
          allocateRelation(part.subVec.asInstanceOf[Payload].loType.asInstanceOf[lo.Record], partData) +
          allocateRelation(order.subVec.asInstanceOf[Payload].loType.asInstanceOf[lo.Record], orderData)
    }
  }

}
